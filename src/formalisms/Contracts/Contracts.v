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
Require Import Coq.Logic.Decidable.

Section Contracts_Meta_Theory.
(*| .. coq:: |*)

(*|

===============
Contract theory
===============

In this chapter, we mechanize the meta-theory of contracts, along with in Assume/Guarantee instantiation. Definitions follow :cite:`benvenisteContractsSystemsDesign`.

In :cite:`DBLP:journals/corr/abs-2108-13647`, the authors propose a mechanization of these contracts using a set-theoretical approach. In our formalization, we opted for the Coq :coq:`Prop` type instead.


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
    Mc : Model -> Prop;
    Ec : Model -> Prop;
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

Definition refines c' c  :=
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

(*| Two contracts are equivalent iff. they refine each other. |*)

Definition equiv c1 c2 := (c1 ≼ c2) /\ (c2 ≼ c1).

Notation "c1 ≍ c2" := (equiv c1 c2) (at level 70 , no associativity).

(*| :coq:`refines` is reflexive, transitive, and antisymmetric. |*)

Theorem refines_refl : forall c1, c1 ≼ c1.
Proof.
    firstorder.
Qed.

Theorem refines_trans : forall c1 c2 c3,
    c1 ≼ c2 -> c2 ≼ c3 -> c1 ≼ c3.
Proof.
    unfold refines.
    intros c1 c2 c3 H0 H1 m.
    specialize (H0 m) ; destruct H0.
    specialize (H1 m) ; destruct H1.
    split ; auto.
Qed.

Theorem refines_antisym : forall c1 c2,
    c1 ≼ c2 -> c2 ≼ c1 -> c1 ≍ c2.
Proof.
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

Definition contract_composition_well_defined' (* XXX *)
    (c1 c2: Contract)
    : Prop
:=
    forall (m1 m2 e: Model),
        (m1 ⊢m c1) /\ (m2 ⊢m c2) /\ (e ⊢e (c1 ⊗ c2)) ->
        ((m1 × m2) ⊢m (c1 ⊗ c2)) /\ ((e × m2) ⊢e c1) /\ ((e × m1) ⊢e c2).

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
    apply refines_compatible with (c:=c1 ⊗ c2 ) ; auto.
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
    simpl.
    firstorder.
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
(*| .. coq:: |*)
