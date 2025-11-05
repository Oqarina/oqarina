.. coq::


.. coq:: none

   Require Import Coq.Relations.Relation_Definitions.
   Require Import Coq.Lists.List.
   Import ListNotations. (* from List *)

   Require Import Coq.Bool.Bool.
   Require Import Coq.Classes.SetoidClass.
   Open Scope equiv_scope.

   Require Import Coq.Logic.Decidable.
   Require Import Coq.Logic.FunctionalExtensionality.
   Require Import Coq.Logic.PropExtensionality.
   Set Implicit Arguments.
   Set Strict Implicit.

   Require Import Oqarina.CoqExt.all.
   Require Import Oqarina.formalisms.Contracts.Specification.

   Section Contracts_Meta_Theory.

   Import Specifications_Notations.

Contract meta-theory
====================

Let us consider a model, that implements the :coq:`Specification` typeclass, extended with a partial composition operator.

.. coq::

   Variable model : Type.
   Context `{spec : Specification model}.

We define a contract as a pair of two functions that computes, for a model, the sets of models that implement the contract (:coq:`Mc`) and the set of models that are compatible with the contract (:coq:`Ec`) as per :cite:`benvenisteContractsSystemsDesign`, section 3.2.

Rationale: the original paper provides little fundations for the definition of contracts. In the following, we define a contract by a function :coq:`Model -> Prop`. A model validates C iff :coq:`Mc C` and :coq:`Ec C` are True.

*Note: we impose the contracts to be decidable. This is a strong hypothesis, but necessary to compose models as one needs a contract to be either true or false. Requesting decidability makes it possible to reason and compute on contracts easily.*

.. coq::

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

A contract having no implementation is called inconsistent. A contract having no environment is called incompatible.

.. coq::

   Definition Inconsistent_Contract (C : Contract) :=
       forall m: model, ~ C.(Mc) m.

   Definition Incompatible_Contract (C : Contract) :=
       forall m: model, C.(Ec) m = False.

We define notations for a model that implements a contract, and an environment that is compatible with a contract.

.. coq::

   Definition Implements_Contract m c := c.(Mc) m.

   Notation "m ⊢m c" := (Implements_Contract m c)
       (at level 70, no associativity).

   Definition Is_Compatible_Contract e c := c.(Ec) e.

   Definition Compatible_Contract c :=
       exists e, Is_Compatible_Contract e c.

   Notation "e ⊢e c" := (Is_Compatible_Contract e c)
       (at level 70, no associativity).

Contract refinement
-------------------

A contract refines another if it follows Liskow-like principles on :coq:`Mc` and :coq:`Ec`.

.. coq::

   Definition refines c' c :=
       forall m, (m ⊢m c' -> m ⊢m c) /\ (m ⊢e c -> m ⊢e c' ).

:coq:`refines` is a pre-order, it implements the :coq:`Refinement` typeclass.

.. coq::

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

Additional results.

.. coq::

   Lemma refines_implements: forall c' c m,
       c' ≼ c -> m ⊢m c' -> m ⊢m c.
   Proof.
       simpl.
       unfold refines.
       intros.
       specialize (H m).
       intuition.
   Qed.

   Lemma refines_compatible: forall c' c m,
       c' ≼ c -> m ⊢e c -> m ⊢e c'.
   Proof.
       simpl.
       unfold refines.
       intros.
       specialize (H m).
       intuition.
   Qed.

Contract equivalence
--------------------

Two contracts are equivalent iff. they refine each other. :coq:`equiv`
is an equivalence relation.

.. coq::

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

A contract refinement can be extended to a partial order thanks
to the equivalence relation on contracts.

.. coq::

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

Contract composition
--------------------

.. coq::

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
       specialize (H0 m).
       specialize (H m).

       split ;
           unfold contract_compose ; simpl ; intuition.
   Qed.

   #[global] Instance Composition_Contract : Composition := {
       compose := contract_compose ;
       compose_compatible := Property_3a ;
       compose_assoc := compose_contract_Setoid_SemiGroup ;
       compose_comm := compose_contract_Setoid_Commutative ;
   }.

A consequence of the above results is that :coq:`Contract` is a :coq:`Specification`

.. coq::

   #[global] Instance Specification_Contract : Specification := {
       m := Model_Contract;
       refinement_op := Refinement_Contract ;
       compose_op := Composition_Contract;
   }.

Contract compatibility
----------------------

From table 2, "Say that (C1, C2) is a compatible pair if C1 × C2 is compatible". XXX this

.. coq::

   Definition contract_composition_well_defined
       (c1 c2: Contract)
       : Prop
   :=
       forall (m1 m2 e: model),
           (m1 ⊢m c1) /\ (m2 ⊢m c2) -> (valid (m1 × m2)).

   Definition contracts_compatible c1 c2 :=
       Compatible_Contract (c1 × c2).

Contract conjunction
--------------------

The authors define the Greatest Lower Bound of contract refinement (:cite:`benvenisteContractsSystemsDesign`, section 3.3). Because of our encoding, we provide a more direct definition based on conjunction and disjunction of propositions.

.. coq::

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
       specialize (H m).
       split ; firstorder.
   Qed.

Additional results
------------------

.. coq::

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

Corrollary 2 states that compose is associate and commutative.

.. coq:: none

   End Contracts_Meta_Theory.

   Module Contract_Notations.

       Notation "m ⊢m c" := (Implements_Contract m c)
           (at level 70, no associativity).

       Notation "e ⊢e c" := (Is_Compatible_Contract e c)
           (at level 70, no associativity).

   End Contract_Notations.
