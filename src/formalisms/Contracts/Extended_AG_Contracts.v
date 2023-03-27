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

Require Import Oqarina.CoqExt.all.
Require Import Oqarina.formalisms.Contracts.Specification.
Require Import Oqarina.formalisms.Contracts.MetaTheory.
Require Import Oqarina.formalisms.Contracts.AG_Contracts.
(*| .. coq:: |*)

(*|
Extended A/G Contracts
======================

In this section, we extend A/G contracts to rich specifications.

|*)

(*| .. coq:: none |*)
Section Extended_AG_Contract.
(*| .. coq:: |*)

Import AG_Contract_Notations.
Import Specifications_Notations.

(*| Assume a type M denoting a rich specification (or model) |*)
Variable M : Type.
Context `{spec_m : Rich_Specification M}.

(*| Assume a type V denoting a specification, forming a class of Assume/Guarantee contracts. |*)
Variable V : Type.
Context `{spec_v : Specification V}.

(*| We defined an extended A/G contract as a pair of a function mapping
a model to a variable V and a A/G contract. |*)

Record Extended_AG_Contract := {
    phi : M -> V ;
    ag_contract : AG_Contract V;
}.

Definition Model_Implements_Contract (m : M) (c : Extended_AG_Contract) :=
    let c' := @ (Saturate c.(ag_contract)) in
        c.(phi) m ⊢m c'.

(*| We say that a refinement m of a model m' is *preserving*  a contract c
if both m and m' both implement the contract c. A sufficient conditition is
phi (m) = phi (m'). |*)

Lemma Refinement_Preserving_Contract: forall (m m': M) (c : Extended_AG_Contract),
    m ≼ m' -> c.(phi) m = c.(phi) m'
        -> Model_Implements_Contract m c
        -> Model_Implements_Contract m' c.
Proof.
    unfold Model_Implements_Contract.
    intros.
    rewrite <- H0.
    apply H1.
Qed.

(*| We say that a refinement m of a model m' is *robust* w.r.t. a contract c
if both m and m' both implement the contract c but phi (m) <> phi (m'). |*)

Definition Refinement_Robust (m m': M) (c : Extended_AG_Contract) : Prop :=
    m ≼ m' -> c.(phi) m <> c.(phi) m'
        -> Model_Implements_Contract m c
        -> Model_Implements_Contract m' c.

(*| We say that a refinement m of a model m' is *preserved* by a refined contract c' of contrac c
if both m and m' both implement the contract c. A sufficient conditition is
phi (m) = phi (m'). |*)

Definition Refinement_Refined_Contract (m m': M) (c : Extended_AG_Contract) : Prop :=
    exists c',
        m ≼ m' -> (@ c'.(ag_contract)) ≼ (@ c.(ag_contract))
            -> Model_Implements_Contract m c
            -> Model_Implements_Contract m' c'.

End Extended_AG_Contract.