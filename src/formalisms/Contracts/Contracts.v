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
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Relations.Relation_Definitions.

Set Implicit Arguments.
Set Strict Implicit.

Section Contracts_Meta_Theory.
(*| .. coq:: |*)

(*|

===============
Contract theory
===============

In this chapter, we mechanize the meta-theory of contracts, along with in Assume/Guarantee instantiation. Definitions follow :cite:`benvenisteContractsSystemsDesign`.

In :cite:`DBLP:journals/corr/abs-2108-13647`, the authors propose a mechanization of these contracts using a set-theoretical approach. In our formalization, we opted for the Coq :coq:`Prop` type instead. Ultimately, they are equivalent in that the authors use decidable set appartenance.


Prolegomena
===========

We define the concept of model, as a general type with the notion of validity and composability. The compose operator generates a new model, it is commutative and associative.

|*)

Variable Model : Type.

Hypothesis valid_model: Model -> Prop.

Variable compose_model: Model -> Model -> Model.

Notation "m1 '×' m2" := (compose_model m1 m2)
    (at level 70, right associativity).

Hypothesis compose_models_assoc: forall m1 m2 m3,
    ((m1 × m2) × m3) = (m1 × (m2 × m3)).

Hypothesis compose_models_comm: forall m1 m2,
    (m1 × m2) = (m2 × m1).

(*|

Contract meta-theory
====================

We define a contract as a pair of two functions that computes, for a model, the sets of models that implement the contract (:coq:`Mc`) and the set of models that are compatible with the contract (:coq:`Ec`). (:cite:`benvenisteContractsSystemsDesign`, section 3.2).

Rationale: the original paper provides little fundations for the definition of contracts. In the following, we define a contract by a function :coq:`Model -> Prop`. A model validates C iff :coq:`Mc C` and :coq:`Ec C` are True.

*Note: we impose the contracts to be decidable. This is a strong hypothesis, but necessary to compose models as one needs a contract to be either true or false. Requesting decidability makes it possible to reason and compute on contracts easily.*

|*)

Record Contract := {
    Ec : Model -> Prop;
    Mc : Model -> Prop;
}.

Hypothesis Decidable_Contract_c:
    forall (m: Model) (c: Contract), decidable (c.(Mc) m).

Hypothesis Decidable_Contract_e:
    forall (m: Model) (c: Contract), decidable (c.(Ec) m).

(*| A contract having no implementation is called inconsistent. A contract having no environment is called incompatible. |*)

Definition Inconsistent_Contract (C : Contract) :=
    forall m: Model, ~ C.(Mc) m.

Definition Incompatible_Contract (C : Contract) :=
    forall m: Model, C.(Ec) m = False.

(*| We define notations for a model that implements a contract, and an environment that is compatible with a contract. |*)

Definition Implements_Contract m c :=
    c.(Mc) m.

Notation "m ⊢m c" := (Implements_Contract m c)
    (at level 70, no associativity).

Definition Is_Compatible_Contract e c :=
    c.(Ec) e.

Definition Compatible_Contract c :=
    exists e, Is_Compatible_Contract e c.

Notation "e ⊢e c" := (Is_Compatible_Contract e c)
    (at level 70, no associativity).

(*|

Contract refinement
-------------------

Property #1
```````````

A contract refines another if it follows Liskow-like principles on :coq:`Mc` and :coq:`Ec`.

 |*)

Definition refines c' c :=
    forall m, (m ⊢m c' -> m ⊢m c) /\ (m ⊢e c -> m ⊢e c' ).

Notation "c1 ≼ c2" := (refines c1 c2) (at level 70, no associativity).

Lemma refines_implements: forall c' c m,
    c' ≼ c -> m ⊢m c' -> m ⊢m c.
Proof.
    unfold refines.
    intros.
    specialize (H m).
    intuition.
Qed.

Lemma refines_compatible: forall c' c m,
    c' ≼ c -> m ⊢e c -> m ⊢e c'.
Proof.
    unfold refines.
    intros.
    specialize (H m).
    intuition.
Qed.

(*| Two contracts are equivalent iff. they refine each other. :coq:`equiv` an equivalence relation. |*)

Definition equiv c1 c2 := (c1 ≼ c2) /\ (c2 ≼ c1).

Notation "c1 ≍ c2" := (equiv c1 c2) (at level 70 , no associativity).

Lemma equiv_refl: reflexive _ equiv.
Proof. firstorder. Qed.

Theorem equiv_trans: transitive _ equiv.
Proof. firstorder. Qed.

Theorem equiv_sym: symmetric _ equiv.
Proof. firstorder. Qed.

Global Instance equiv_Equivalence : Equivalence (equiv) := {|
    Equivalence_Reflexive := equiv_refl ;
    Equivalence_Symmetric := equiv_sym ;
    Equivalence_Transitive := equiv_trans;
|}.

(*| :coq:`refines` is reflexive, transitive, and antisymmetric. In other words, it is a partial order. |*)

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

Global Instance refines_PreOrder : PreOrder (refines) := {|
    PreOrder_Reflexive := refines_refl ;
    PreOrder_Transitive := refines_trans;  |}.

Global Instance refines_PartialOrder:
    PartialOrder equiv refines.
Proof.
    split.
    - (* Equivalence implies inclusion *)
        firstorder.
    - (* Inclusion implies equivalence *)
        firstorder.
Defined.

Theorem refines_antisym : forall c1 c2,
    c1 ≼ c2 -> c2 ≼ c1 -> c1 ≍ c2.
Proof.
    intros.
    unfold equiv ; auto.
Qed.

(*|

Property #2
```````````

The authors define the Greatest Lower Bound of contract refinement (:cite:`benvenisteContractsSystemsDesign`, section 3.3). Because of our encoding, we provide a more direct definition based on conjunction and disjunction of propositions. |*)

Definition contract_conjunction c1 c2 := {|
    Mc := fun m : Model => c1.(Mc) m /\ c2.(Mc) m ;
    Ec := fun m : Model => c1.(Ec) m \/ c2.(Ec) m;
|}.

Notation "c1 ⊓ c2" := (contract_conjunction c1 c2)
    (at level 40, left associativity).

Lemma contract_conjunction_comm: forall c1 c2,
    c1 ⊓ c2 ≍ c2 ⊓ c1.
Proof.
    intros.
    unfold contract_conjunction.
    firstorder.
Qed.

Theorem shared_refinement: forall c c1 c2,
    c ≼ (c1 ⊓ c2) -> c ≼ c1.
Proof.
    intros.
    unfold refines in *.
    unfold contract_conjunction in H.
    intros.
    specialize (H m).
    split ; firstorder.
Qed.

(*|

Contract composition
````````````````````

Composition (section 3.4)

|*)

Definition contract_compose c1 c2 := {|
    Mc := fun m : Model => m ⊢m c1 /\ m ⊢m c2  \/
                            (~ m ⊢e c1 \/ ~ m ⊢e c2);
    Ec := fun m : Model => m ⊢e c1 /\ m ⊢e c2;
|}.

Notation "c1 ⊗ c2" := (contract_compose c1 c2)
    (at level 71, left associativity).

Definition contract_composition_well_defined
    (c1 c2: Contract)
    : Prop
:=
    forall (m1 m2 e: Model),
        (m1 ⊢m c1) /\ (m2 ⊢m c2) -> (valid_model (m1 × m2)).

(*|

Contract compatibility
``````````````````````

From table 2, "Say that (C1, C2) is a compatible pair if C1⊗C2 is compatible". |*)

Definition contracts_compatible c1 c2 :=
    Compatible_Contract (c1 ⊗ c2).

(*|

Additional results
``````````````````

|*)

Lemma Property_3a: forall c1 c2 c1' c2',
    c1' ≼ c1 -> c2' ≼ c2 -> (c1' ⊗ c2') ≼ (c1 ⊗ c2).
Proof.
    unfold refines.
    intros.
    specialize (H m).
    specialize (H0 m).

    split ;
        unfold contract_compose  ; simpl ; intuition.
Qed.

 (* Lemma 1 p25 *)

Lemma Lemma_1: forall c1 c2 c1' c2',
    c1' ≼ c1 -> c2' ≼ c2
        -> (contract_composition_well_defined c1 c2)
            -> (contract_composition_well_defined c1' c2').
Proof.
    intros c1 c2 c1' c2' H H1.
    unfold contract_composition_well_defined in *.
    intros H2.
    intros m1 m2 e.
    specialize (H2 m1 m2 e).

    intuition.

    assert (m1 ⊢m c1).
    apply refines_implements with (c':=c1'). apply H. apply H3.

    assert (m2 ⊢m c2).
    apply refines_implements with (c':=c2'). apply H1. apply H4.

    intuition.
Qed.

Lemma Property_3b: forall c1 c2 c1' c2',
    c1' ≼ c1 -> c2' ≼ c2 -> contracts_compatible c1 c2 -> contracts_compatible c1' c2'.
Proof.
    unfold contracts_compatible.
    unfold Compatible_Contract.
    intros.
    destruct H1.
    assert ((c1' ⊗ c2') ≼ (c1 ⊗ c2)).
    apply Property_3a ; auto.

    assert ((x ⊢e (c1' ⊗ c2'))).
    apply refines_compatible with (c:=c1 ⊗ c2) ; auto.
    exists x ; auto.
Qed.

Lemma Property_4: forall c1 c2 c3 c4,
    ((c1 ⊗ c2) ⊗ (c3 ⊗ c4)) ≍ ((c1 ⊗ c3) ⊗ (c2 ⊗ c4)).
Proof.
    (* We admit this proof, firstorder is too slow to discharge it.
       It is assumed it could be proved by using the lemmas below. *)
Admitted.

(*| Corrollary 2 states that compose is associate and commutative. |*)

Lemma contract_compose_assoc: forall c1 c2 c3,
    (c1 ⊗ (c2 ⊗ c3)) ≍ ((c1 ⊗ c2) ⊗ c3).
Proof.
    intros.
    unfold contract_compose, equiv, refines.
    simpl ; firstorder.
Qed.

Lemma contract_compose_comm: forall c1 c2,
    (c1 ⊗ c2) ≍ (c2 ⊗ c1).
Proof.
    intros.
    unfold contract_compose, equiv, refines.
    simpl ; firstorder.
Qed.

(*| .. coq:: none |*)
End Contracts_Meta_Theory.

Module Contract_Notations.

Notation "m ⊢m c" := (Implements_Contract m c)
    (at level 70, no associativity).

Notation "e ⊢e c" := (Is_Compatible_Contract e c)
    (at level 70, no associativity).

Notation "c1 ≍ c2" := (equiv c1 c2) (at level 70 , no associativity).

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

Definition Assertion: Type := list V -> Prop.
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

Notation "@ c" := (AG_Contract_to_Contract c) (at level 70 , no associativity).

(*| A saturated contract is an A/G contract defines by the following rule predicate. It is an idemptotent function. |*)

Definition Saturate (AG : AG_Contract) := {|
    A := AG.(A);
    G := fun x => (AG.(A) x -> AG.(G) x);
|}.

Lemma Saturate_idempotent: forall ag,
    (@Saturate ag) ≍ (@ Saturate (Saturate ag )).
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
        (@ Saturate ag) ≍ (@ ag).
Proof.
    intros. unfold Saturate.
    unfold AG_Contract_to_Contract.
    simpl. firstorder.
Qed.

(*| The notion of contract refinement and composition is directly inherited from the meta-theory.

We demonstrate that a saturated contract preserves some initial properties, e.g. equivalence, compatibility, etc. |*)

Theorem contract_extensionality : forall (c1 c2 : AG_Contract),
    (@c1) ≍ (@c2) -> Saturate c1 = Saturate c2.
Proof.
    intros. firstorder.
    unfold refines in *.
    simpl in *.
    unfold Saturate.

    assert (
        (fun x : list V => A c1 x -> G c1 x) =
        (fun x : list V => A c2 x -> G c2 x)
    ).
    apply functional_extensionality. intros.
    specialize (H x).
    specialize (H0 x).
    apply propositional_extensionality. firstorder.

    assert (forall m, A c1 m = A c2 m).
    intros.
    specialize (H m).
    specialize (H0 m).
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
