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
From mathcomp Require Import finset fintype ssrbool eqtype.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Utf8.

(*| .. coq::  |*)

(*|
Extensions to finset
=====================

The following extends finsets with trivial lemmas.

|*)

Section finset_Ext.

Variable t : finType.
Definition set_t : Type := { set t }.

Lemma disjoint_set0 : forall (s : set_t), [disjoint s & set0].
Proof.
    intros.
    rewrite <- setI_eq0 ; rewrite setI0 ; intuition.
Qed.

Lemma disjointU: forall A B C : set_t,
    [disjoint A & B] -> [disjoint A & C] -> [disjoint A & B :|: C].
Proof.
    intros A B C HA HB.
    rewrite <- setI_eq0.
    rewrite <- setI_eq0 in HA.
    rewrite <- setI_eq0 in HB.
    rewrite setIUr.
    rewrite setU_eq0.
    auto with *.
Qed.

Lemma disjointU2: forall A B C D: set_t,
    [disjoint A & B] -> [disjoint C & D] ->
    [disjoint B & C] -> [disjoint D & A] ->
    [disjoint A :|: C & B :|: D].
Proof.
    intros A B C D HAB HCD HBC HDA.
    apply disjointU.
    - rewrite disjoint_sym. apply disjointU.
    + now rewrite disjoint_sym.
    + trivial.
    - rewrite disjoint_sym. apply disjointU.
    + trivial.
    + now rewrite disjoint_sym.
Qed.

Lemma in_set_set0 (S : set_t) (x: t) :
  x \in S -> S != set0.
Proof.
  case (set_0Vmem S) => [?|[x1 ini]].
  - subst. rewrite in_set0. intuition.
  - intros. apply (introT (set0Pn S)). now exists x.
Qed.

Lemma orb_True1 b1 b2 : b1 || b2 = true ↔ b1 ∨ b2.
Proof. destruct b1, b2 ; simpl ; tauto. Qed.

Lemma orb_True2 b1 b2 : b1 || b2 ↔ b1 ∨ b2.
Proof.
    assert (b1 || b2 <-> (b1 || b2) = true) ; auto with *.
    eapply orb_True1.
Qed.

Lemma disjoint_in (A B C: set_t) (x:t):
    [disjoint B & C] ->
    x \in A :|: B -> x \in A :|: C -> x \in A.
Proof.
    intros.
    rewrite in_setU in *.
    rewrite orb_True2 in *.
    destruct H0, H1 ; trivial.
    assert (x \in B = false).
    eapply disjointFl. apply H. trivial.
    rewrite H0 in H2.
    intuition.
Qed.

End finset_Ext.
