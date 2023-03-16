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
Require Import Coq.Relations.Relation_Operators.
(*| .. coq::  |*)

(*|

.. index:: transitive closue, CoqExt; clos_refl_trans_1n, CoqExt; rt1n_trans'

Relations, transitive closures
==============================

For a relation :coq:`R`, :coq:`clos_refl_trans_1n` defines the notion of direct reflexive-transitive closure on the left of this relation.

We extend Coq standard library :coq:`Coq.Relations.Relation_Operators` with additional results, as suggested in the course "Mechanized semantics" given by Xavier Leroy at Collège de France in 2019-2020. Although a Coq development serves as a companion for this class, we propose a different set of definitions that builds on top of the Coq standard library.

|*)

(*| .. coq:: none |*)
Section Reflexive_Transitive_Closure_Ext.
(*| .. coq:: |*)

Variable A: Type.
Variable R: relation A.

Lemma rt1n_trans': forall (a b: A) ,
    clos_refl_trans_1n A R a b ->
        forall c, clos_refl_trans_1n A R b c ->
        clos_refl_trans_1n A R a c.
Proof.
    intros.
    induction H.
    - apply H0.
    - eapply rt1n_trans. apply H. auto.
Qed.

(*| We define the transitive closure of a relation from :coq:`clos_refl_trans_1n`. This allows one to reason on zero, one, or many steps (:coq:`clos_refl_trans_1n_star`), or one or many (:coq:`clos_refl_trans_1n_plus`). This is important for definiing equivalences between relations. |*)

Inductive clos_refl_trans_1n_plus : A -> A -> Prop :=
  | plus_trans: forall a b c,
      R a b -> clos_refl_trans_1n A R b c -> clos_refl_trans_1n_plus a c.

Lemma clos_refl_trans_1n_plus_one:
  forall a b, R a b -> clos_refl_trans_1n_plus a b.
Proof.
    intros.
    eapply plus_trans.
    - apply H.
    - apply rt1n_refl.
Qed.

Lemma clos_refl_trans_1n_plus_star: forall a b,
    clos_refl_trans_1n_plus a b -> clos_refl_trans_1n A R a b.
Proof.
    intros. inversion H.
    eapply rt1n_trans.
    - apply H0.
    - apply H1.
Qed.

(*| .. coq:: none |*)
End Reflexive_Transitive_Closure_Ext.
(*| .. coq:: |*)
