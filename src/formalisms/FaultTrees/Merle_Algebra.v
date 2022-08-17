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
Require Import Coq.Unicode.Utf8.
Require Import Coq.NArith.Ndist.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.

Require Import Oqarina.core.all.
Import NaturalInfTime.
Require Import Oqarina.formalisms.FaultTrees.NatInfMinMax.

Require Import Oqarina.cpdttactics.
(*| .. coq:: |*)

(*|

#############
Merle Algebra
#############

In this section, we define the Temporal model of Boolean operators as presented in Merle's PhD thesis [XXX]

|*)

Section Merle_Algebra.

Variable basic_event : Type.

Definition d := basic_event -> Time.

(*| :coq:`d_plus` and :coq:`d_prod` are defined in terms of min and max operators |*)

Definition d_plus (d1 d2 : d)  : d :=
    (fun b => ni_min (d1 b) (d2 b)).

Definition d_prod (d1 d2 : d) : d :=
    (fun b => ni_max (d1 b) (d2 b)).

Definition d_0 : d := (fun b : basic_event => (ni 0)).

Definition d_inf : d := (fun b : basic_event => infty).

Notation "⊥" := d_inf.
Notation "⊤" := d_0.

(*| In the following, we prove all lemmas, numerotation follows the original manuscript. |*)

(*| This auxiliary lemma proves lemmas in the form forall d1, d2, .., (f d1 d2 ..) = (g d1 d2 ..) rom lemma in the form of forall b (f d1 d2 ..) b = (g d1 d2 ..) b. |*)

Ltac prove_extensionality_from_lemma name :=
    intros ; pose proof name ;
    apply functional_extensionality; auto.

(*| (3.1) d_plus is commutative |*)

Lemma d_plus_comm_b: forall (d1 d2 : d) (b:basic_event),
    d_plus d1 d2 b = d_plus d2 d1 b.
Proof.
    intros ; unfold d_plus.
    apply ni_min_comm.
Qed.

Lemma d_plus_comm: forall (d1 d2 : d),
    d_plus d1 d2 = d_plus d2 d1.
Proof.
    prove_extensionality_from_lemma d_plus_comm_b.
Qed.

(*| (3.2) d_prod is commutative |*)

Lemma d_prod_comm_b: forall (d1 d2 : d) (b:basic_event),
    d_prod d1 d2 b = d_prod d2 d1 b.
Proof.
    intros ; unfold d_plus.
    apply ni_max_comm.
Qed.

Lemma d_prod_comm: forall (d1 d2 : d),
    d_prod d1 d2 = d_prod d2 d1.
Proof.
    prove_extensionality_from_lemma d_prod_comm_b.
Qed.

(*| (3.3) d_plus is associative. This is proved in two steps, for both left and right associativity *)

Lemma d_plus_associative_l_b :
    forall (d1 d2 d3:d) (b:basic_event),
        d_plus (d_plus d1 d2) d3 b = d_plus d1 (d_plus d2 d3 ) b.
Proof.
    intros ; unfold d_plus.
    apply ni_min_assoc.
Qed.

Lemma d_plus_associative_l :
forall (d1 d2 d3:d), d_plus (d_plus d1 d2) d3 = d_plus d1 (d_plus d2 d3 ).
Proof.
    prove_extensionality_from_lemma d_plus_associative_l_b.
Qed.

Lemma d_plus_associative_r_b:
    forall (d1 d2 d3:d) (b:basic_event),
        d_plus d1 (d_plus d2 d3) b = d_plus (d_plus d1 d2) d3 b.
Proof.
    intros ; unfold d_plus.
    apply ni_min_assoc_r.
Qed.

Lemma d_plus_associative_r :
forall (d1 d2 d3:d), d_plus d1 (d_plus d2 d3) = d_plus (d_plus d1 d2) d3.
Proof.
    prove_extensionality_from_lemma d_plus_associative_r_b.
Qed.

(*| (3.4) d_plus is associative. This is proved in two steps, for both left and right associativity *)

Lemma d_prod_associative_r_b :
    forall (d1 d2 d3:d) (b:basic_event),
        d_prod (d_prod d1 d2) d3 b = d_prod d1 (d_prod d2 d3 ) b.
Proof.
    intros ; unfold d_prod.
    apply ni_max_assoc.
Qed.

Lemma d_prod_associative_r: forall (d1 d2 d3 : d),
    d_prod d1 (d_prod d2 d3) = d_prod (d_prod d1 d2) d3.
Proof.
    prove_extensionality_from_lemma d_prod_associative_r_b.
Qed.

Lemma d_prod_associative_l_b :
    forall (d1 d2 d3:d) (b:basic_event),
        d_prod d1 (d_prod d2 d3) b = d_prod (d_prod d1 d2) d3 b.
Proof.
        intros ; unfold d_prod.
        apply ni_max_assoc_r.
Qed.

Lemma d_prod_associative_l: forall (d1 d2 d3 : d),
    d_prod (d_prod d1 d2) d3 = d_prod d1 (d_prod d2 d3).
Proof.
    prove_extensionality_from_lemma d_prod_associative_l_b.
Qed.

(*| (3.5} d_plus is idempotent *)

Lemma d_plus_idem_b:
forall (d1:d) (b:basic_event), d_plus d1 d1 b = d1 b.
Proof.
    intros.
    unfold d_plus.
    apply ni_min_idemp.
Qed.

Lemma d_plus_idem:
forall (d1:d), d_plus d1 d1 = d1.
Proof.
    prove_extensionality_from_lemma d_plus_idem_b.
Qed.

(*| (3.6} d_prod is idempotent *)

Lemma d_prod_idem_b:
    forall (d1:d) (b:basic_event), d_prod d1 d1 b = d1 b.
Proof.
    intros.
    unfold d_prod.
    apply ni_max_idemp.
Qed.

Lemma d_prod_idem:
forall (d1:d), d_prod d1 d1 = d1.
Proof.
    prove_extensionality_from_lemma d_prod_idem_b.
Qed.

(*| (3.7} d_prod/d_plus distributivity  *)

Lemma d_3_7_b:
    forall (d1 d2 d3:d) (b:basic_event),
        d_prod d1 (d_plus d2 d3) b = d_plus (d_prod d1 d2) (d_prod d1 d3) b.
Proof.
    intros.
    unfold d_prod.
    unfold d_plus.
    apply max_min_distrb.
Qed.

Lemma d_3_7:
    forall (d1 d2 d3:d),
        d_prod d1 (d_plus d2 d3) = d_plus (d_prod d1 d2) (d_prod d1 d3).
Proof.
    prove_extensionality_from_lemma d_3_7_b.
Qed.

Lemma d_3_8_b:
    forall (d1 : d) (b:basic_event), d_plus d1 ⊥ b = d1 b.
Proof.
    intros.
    unfold d_plus, d_inf.
    rewrite ni_min_inf_r ; auto.
Qed.

Lemma d_3_8:
    forall (d1 : d), d_plus d1 ⊥ = d1.
Proof.
    prove_extensionality_from_lemma d_3_8_b.
Qed.

Lemma d_3_8_r:
    forall (d1 : d), d_plus ⊥ d1 = d1.
Proof.
    intros.
    rewrite d_plus_comm.
    apply d_3_8.
Qed.

Lemma d_3_9_b:
    forall (d1 : d) (b:basic_event), d_prod d1 ⊤ b = d1 b.
Proof.
    intros.
    unfold d_prod, d_0.
    rewrite ni_max_0_r ; auto.
Qed.

Lemma d_3_9:
    forall (d1 : d), d_prod d1 ⊤ = d1.
Proof.
    prove_extensionality_from_lemma d_3_9_b.
Qed.

Lemma d_3_9_r:
    forall (d1 : d), d_prod ⊤ d1 = d1.
Proof.
    intros.
    rewrite d_prod_comm.
    apply d_3_9.
Qed.

Lemma d_3_10_b:
    forall (d1 : d) (b:basic_event), d_prod d1 ⊥ b = ⊥ b.
Proof.
    intros.
    unfold d_prod, d_inf.
    rewrite ni_max_inf_r ; auto.
Qed.

Lemma d_3_10: forall (d1 : d), d_prod d1 ⊥ = ⊥.
Proof.
    prove_extensionality_from_lemma d_3_10_b.
Qed.

Lemma d_3_11_b:
forall (d1 d2 d3:d) (b:basic_event),
    d_plus d1 (d_prod d2 d3) b = d_prod (d_plus d1 d2) (d_plus d1 d3) b.
Proof.
    intros.
    unfold d_prod.
    unfold d_plus.
    apply min_max_distrb.
Qed.

Lemma d_3_11:
forall (d1 d2 d3:d),
    d_plus d1 (d_prod d2 d3) = d_prod (d_plus d1 d2) (d_plus d1 d3).
Proof.
    prove_extensionality_from_lemma d_3_11_b.
Qed.

Lemma d_3_12_b:
    forall (d1 : d) (b:basic_event), d_plus d1 ⊤ b = ⊤ b.
Proof.
    intros.
    unfold d_plus, d_0.
    rewrite ni_min_O_r ; auto.
Qed.

Lemma d_3_12:
forall (d1 : d), d_plus d1 ⊤ = ⊤ .
Proof.
    prove_extensionality_from_lemma d_3_12_b.
Qed.

Lemma d_3_13_b:
    forall (d1 d2:d) (b:basic_event), d_plus d1 (d_prod d1 d2) b = d1 b.
Proof.
    intros.
    unfold d_plus, d_prod.
    destruct (d1 b); destruct (d2 b) ; simpl ; auto.
    apply f_equal.
    apply PeanoNat.Nat.max_min_absorption.
Qed.

Lemma d_3_13: forall (d1 d2:d), d_plus d1 (d_prod d1 d2) = d1.
Proof.
    prove_extensionality_from_lemma d_3_13_b.
Qed.

Lemma d_3_14_b:
    forall (d1 d2:d) (b:basic_event), d_prod d1 (d_plus d1 d2) b = d1 b.
Proof.
    intros.
    unfold d_plus, d_prod.
    destruct (d1 b); destruct (d2 b) ; simpl ; auto.
    - apply f_equal. apply Max.max_idempotent.
    - apply f_equal. apply PeanoNat.Nat.min_max_absorption.
Qed.

Lemma d_3_14:
    forall (d1 d2:d), d_prod d1 (d_plus d1 d2) = d1.
Proof.
    prove_extensionality_from_lemma d_3_14_b.
Qed.

(*| Before, Simulatanerous, and Inclusive Before operators |*)

Definition d_before (d1 d2 : d) : d :=
    (fun b =>
    match compare' (d1 b) (d2 b) with
    | Lt => d1 b
    | Eq => d_inf b
    | Gt => d_inf b
    end).

Definition d_simultaneous (d1 d2 : d) : d :=
    (fun b =>
        match compare' (d1 b) (d2 b) with
        | Lt => d_inf b
        | Eq => d1 b
        | Gt => d_inf b
    end).

Definition d_incl_before (d1 d2 : d) : d :=
    (fun b =>
        match compare' (d1 b) (d2 b) with
        | Lt => d1 b
        | Eq => d1 b
        | Gt => d_inf b
    end).

Notation "a '＋' b" := (d_plus a b) (at level 90).

Notation "a '✕' b" := (d_prod a b) (at level 90).

Notation "a '△' b" := (d_simultaneous a b) (at level 90).

Notation "a '◁' b" := (d_before a b) (at level 90).

Notation "a '◁̳' b" := (d_incl_before a b) (at level  90).

Lemma d_3_16_b: forall (d1 d2 : d) (b : basic_event),
     (d1 ◁̳ d2) b = ((d1 ◁ d2) ＋ (d1 △ d2)) b.
Proof.
    intros.
    unfold d_incl_before, d_before, d_simultaneous, d_plus.
    destruct (compare' (d1 b) (d2 b)).
    - rewrite ni_min_inf_l ; auto.
    - rewrite ni_min_inf_r ; auto.
    - auto.
Qed.

Lemma d_3_16: forall (d1 d2 : d),
    (d1 ◁̳ d2) = ((d1 ◁ d2) ＋ (d1 △ d2)).
Proof.
    prove_extensionality_from_lemma d_3_16_b.
Qed.

Lemma d_3_17: forall (d1 d2 : d) (b : basic_event),
    ((d1 ◁ d2) ✕ (d2 ◁ d1)) b = ⊥ b.
Proof.
    intros.
    unfold d_prod, d_before, d_plus.
    case_eq (compare' (d1 b) (d2 b)) ;
    case_eq (compare' (d2 b) (d1 b)) ; auto.
    - intros. rewrite compare_helper_lt' in H0.
        * apply ni_max_inf_r.
        * apply compare_helper_gt' in H0 ; auto.
    - intros. apply compare_helper_gt' in H.
      rewrite H in H0. discriminate.
      - intros. apply ni_max_inf_r.
Qed.


Lemma d_3_20_b: forall (d1 : d) (b : basic_event),
    (⊥ ◁ d1) b = ⊥ b.
Proof.
    intros. unfold d_before.
    destruct (d1 b) ; auto.
 Qed.

 Lemma d_3_20: forall (d1 : d), (⊥ ◁ d1) = ⊥.
Proof.
    prove_extensionality_from_lemma d_3_20_b.
Qed.

Lemma d_3_21_b: forall (d1 : d) (b : basic_event),
    (d1 ◁ ⊥) b = d1 b.
Proof.
    intros. unfold d_before. unfold d_0.
    destruct (d1 b) ; auto.
 Qed.

Lemma d_3_21: forall (d1 : d), (d1 ◁ ⊥) = d1.
Proof.
    prove_extensionality_from_lemma d_3_21_b.
Qed.

Lemma d_3_21_b': forall (d1 : d) (b : basic_event),
    (d1 ◁ ⊤) b = ⊥ b.
Proof.
    intros. unfold d_before. unfold d_0.
    destruct (d1 b). auto.
    simpl.
    induction n ; auto.
 Qed.

 Lemma d_3_21': forall (d1 : d), (d1 ◁ ⊤) = ⊥.
Proof.
    prove_extensionality_from_lemma d_3_21_b'.
Qed.

(*| (3.35) |*)

Lemma d_simultaneous_comm_b: forall (d1  d2: d) (b : basic_event),
    (d1 △ d2) b = (d2 △ d1) b.
Proof.
    intros. unfold d_simultaneous. unfold d_inf. rewrite cmp_antisym.
    case_eq (compare' (d1 b) (d2 b)) ;
    case_eq (compare' (d2 b) (d1 b)) ; auto.
    - intros. apply natinf_compare_eq ; auto.
    - intros. apply natinf_compare_eq in H ; auto.
    - intros. apply natinf_compare_eq in H ; auto.
Qed.

Lemma d_simultaneous_comm: forall (d1  d2: d), (d1 △ d2) = (d2 △ d1).
Proof.
    prove_extensionality_from_lemma d_simultaneous_comm_b.
Qed.

Lemma d_3_37_b: forall (d1 : d) (b : basic_event),
    (d1 △ ⊥) b = ⊥ b.
Proof.
    intros. unfold d_simultaneous. unfold d_inf.
    destruct (d1 b) ; auto.
 Qed.

Lemma d_3_37: forall (d1 : d), (d1 △ ⊥) = ⊥.
Proof.
    prove_extensionality_from_lemma d_3_37_b.
Qed.

Lemma d_3_50_b: forall (d1 : d) (b : basic_event),
     (d1 ◁̳ ⊥) b = d1 b.
Proof.
    intros.
    rewrite d_3_16_b.
    rewrite d_3_21.
    rewrite d_3_37.
    apply d_3_8_b.
Qed.

Lemma d_3_50: forall (d1 : d), (d1 ◁̳ ⊥) = d1.
Proof.
    prove_extensionality_from_lemma d_3_50_b.
Qed.

Lemma d_3_50_b': forall (d1 : d) (b : basic_event),
     (⊤ ◁̳ d1) b = ⊤ b.
Proof.
    intros.
    unfold d_incl_before.
    destruct (d1 b) ; auto.
    induction n ; auto.
Qed.

Lemma d_3_50': forall (d1 : d), (⊤ ◁̳ d1) = ⊤.
Proof.
    prove_extensionality_from_lemma d_3_50_b'.
Qed.

(*| (3.51) d_incl_before is idempotent |*)

Lemma d_incl_before_idem_b:
    forall (d1:d) (b:basic_event), (d1 ◁̳ d1) b = d1 b.
Proof.
    intros.
    unfold d_incl_before.
    assert (compare' (d1 b) (d1 b) = Eq).
    apply natinf_compare_eq' ; auto.
    rewrite H ; auto.
Qed.

Lemma d_incl_before_idem: forall (d1:d), (d1 ◁̳ d1) = d1.
Proof.
    prove_extensionality_from_lemma d_incl_before_idem_b.
Qed.

(*| Definition of DFT gates from Chapter 3 |*)

Definition D_OR := d_plus.

Definition D_AND := d_prod.

Lemma D_AND_TRUE_r:
forall (d1 : d), D_AND d1 ⊤ = d1.
Proof.
    unfold D_AND. apply d_3_9.
Qed.

(*| Definition of DFT gates from Chapter 4 |*)

Definition P_PAND (A B : d) : d := (A ✕ B) ✕ (A ◁̳ B).

Lemma P_PAND_0_d: forall d, P_PAND ⊤ d = d.
Proof.
    intros.
    unfold P_PAND.
    rewrite d_3_9_r.
    rewrite d_3_50'.
    rewrite d_3_9 ; auto.
Qed.

(*| (3.51) d_incl_before is idempotent |*)

Lemma P_PAND_idem_b:
    forall (d1:d) (b:basic_event), P_PAND d1 d1 b = d1 b.
Proof.
    intros.
    unfold P_PAND.

    rewrite d_prod_idem.
    unfold d_plus.
    rewrite d_incl_before_idem.
    rewrite d_prod_idem ; auto.
Qed.

Lemma P_PAND_idem: forall (d1:d), P_PAND d1 d1 = d1.
Proof.
    prove_extensionality_from_lemma P_PAND_idem_b.
Qed.

Definition P_FDEP (T A B: d) : d * d :=
    (( T ＋  A ◁̳ T), ( T ＋  B ◁̳ T) ).

(* This is the model of a SPARE gate with only one spare (B), Ba being the FT for the case B is active, and Bd the FT for the case B is dormant *)

Definition P_SPARE (A Ba Bd : d) : d :=
    (Ba ✕ (A ◁ Ba )) ＋  (A ✕ (Bd ◁  A)).

Definition P_SPARE_Valid (Ba Bd : d) (b : basic_event) :=
    (Ba ✕ Bd) b = ⊥ b.

Lemma P_SPARE_Cold_Spare: forall (A Ba Bd :d),
    Bd = ⊥ -> P_SPARE A Ba Bd = (Ba ✕ (A ◁ Ba )).
Proof.
    intros.
    unfold P_SPARE.
    subst.
    rewrite d_3_20.
    rewrite d_3_10.
    rewrite d_3_8.
    reflexivity.
Qed.

Lemma P_SPARE_Hot_Spare: forall (A Ba Bd :d),
    Bd = Ba -> P_SPARE A Ba Bd = (Ba ＋ A).
Proof.
    intros. subst. unfold P_SPARE.
Admitted.

Definition n_AND (l : list d) :=
    fold_right (fun a b => (D_AND a b)) d_0 l.

Definition n_OR (l : list d) :=
    fold_right (fun a b => (D_OR a b)) d_inf l.

Definition n_PAND (l : list d) :=
    fold_left (fun a b => (P_PAND a b)) l d_0.

Section DFT_Rewriting_Rules.

(*| See Formal Verification of Rewriting Rules for Dynamic Fault Trees
Yassmeen Elderhalli1(B), Matthias Volk2, Osman Hasan1, Joost-Pieter Katoen2, and Sofi`ene Tahar1 from
https://doi.org/10.1007/978-3-030-30446-1_27 |*)

Lemma Rule_1: forall (l1 l2: list d), Permutation l1 l2 -> n_AND l1 = n_AND l2.
Proof.
    apply Permutation_ind_bis ; auto.
    - intros. simpl. rewrite H0. auto.
    - intros. simpl. rewrite H0. unfold D_AND.
      repeat rewrite d_prod_associative_r.
      assert (d_prod x y = d_prod y x). apply d_prod_comm. rewrite H1. auto.
    - intros. rewrite H0. auto.
Qed.

Lemma Rule_2: forall (l1 l2: list d), Permutation l1 l2 -> n_OR l1 = n_OR l2.
Proof.
    apply Permutation_ind_bis ; auto.
    - intros. simpl. rewrite H0. auto.
    - intros. simpl. rewrite H0. unfold D_OR.
      repeat rewrite d_plus_commr. repeat rewrite d_plus_associative_r.
      assert (d_plus x y = d_plus y x). apply d_plus_comm.
      rewrite H1. auto.
    - intros. rewrite H0. auto.
Qed.

Lemma Rule_4: forall d, n_AND [ d ] = d.
Proof.
    simpl. unfold D_AND. apply d_3_9.
Qed.

Lemma Rule_5: forall d, n_OR [ d ] = d.
Proof.
    simpl. unfold D_OR. apply d_3_8.
Qed.

Lemma Rule_7: forall (d1 :d) (b : basic_event), n_PAND [ d1 ] = d1.
Proof.
    intros.
    simpl. unfold n_PAND.
    simpl.
    unfold P_PAND.
    rewrite d_3_9_r.
    rewrite d_3_50'.
    rewrite d_3_9 ; auto.
Qed.

Lemma Rule_8: forall (l1 l2: list d),
    n_AND ([ n_AND l1 ] ++ l2) = n_AND (l1 ++ l2).
Proof.
    intros.
    induction l1.
    - simpl. rewrite d_3_9_r ; auto.
    - simpl in *. rewrite d_prod_associative_l.
      unfold D_AND in IHl1. rewrite IHl1; auto.
Qed.

Lemma Rule_8': forall (a :d) (l1: list d),
    n_AND ([a] ++ [ n_AND l1 ] ) = n_AND (a :: l1).
Proof.
    intros.
    induction l1.
    - simpl ; rewrite d_3_9_r ; auto.
    - simpl ; rewrite d_3_9 ; auto.
Qed.

Lemma Rule_9: forall (l1 l2: list d),
    n_OR  ([ n_OR l1 ] ++ l2) = n_OR (l1 ++ l2).
Proof.
    intros.
    induction l1.
    - simpl. unfold D_OR. rewrite d_3_8_r ; auto.
    - simpl in *. rewrite d_plus_associative_l.
      unfold D_OR in IHl1. rewrite IHl1; auto.
Qed.

Lemma Rule_9': forall (a :d) (l1: list d),
    n_OR ([a] ++ [ n_OR l1 ] ) = n_OR (a :: l1).
Proof.
    intros.
    induction l1.
    - simpl ; rewrite d_3_8_r ; auto.
    - simpl. rewrite d_plus_associative_l.
      rewrite d_3_8 ; auto.
Qed.

Lemma Rule_10: forall (l1 l2: list d),
    n_PAND  ([ n_PAND l1 ] ++ l2) = n_PAND (l1 ++ l2).
Proof.
    intros.
    induction l1 ; simpl; auto.
    - simpl in IHl1.
    unfold n_PAND.
    simpl. rewrite P_PAND_0_d in *. rewrite P_PAND_0_d in *.
    rewrite fold_left_app ; auto.
Qed.

Lemma Rule_11: forall (x : d) (l: list d),
    n_AND  ([ x ; x ]++ l) = n_AND ( [x] ++ l ).
Proof.
    intros.
    simpl.
    unfold D_AND. rewrite d_prod_associative_r.
    rewrite d_prod_idem ; auto.
Qed.

Lemma Rule_12: forall (x : d) (l: list d),
    n_OR  ([ x ; x ]++ l) = n_OR ( [x] ++ l ).
Proof.
    intros.
    simpl.
    unfold D_OR. rewrite d_plus_associative_r.
    rewrite d_plus_idem ; auto.
Qed.

Lemma Rule_13: forall (x : d) (l: list d),
    n_PAND  ([ x ; x ]++ l) = n_PAND ( [x] ++ l ).
Proof.
    intros.
    unfold n_PAND.
    simpl.
    rewrite P_PAND_0_d ; rewrite P_PAND_idem.
    auto.
Qed.

Lemma Rule_14: forall (x y: d), D_AND x (D_OR x y) = x.
Proof.
    intros.
    unfold D_AND, D_OR.
    rewrite d_3_14 ; auto.
Qed.

Lemma Rule_15: forall (x y: d), D_OR x (D_AND x y) = x.
Proof.
    intros.
    unfold D_AND, D_OR.
    rewrite d_3_13 ; auto.
Qed.

Lemma Rule_16: forall (x y z: d),
    D_OR (D_AND x y) (D_AND y z) = D_AND (D_OR x z) y.
Proof.
    intros.
    unfold D_AND, D_OR.
    rewrite d_prod_comm at 1.
    rewrite <- d_3_7.
    rewrite d_prod_comm ; auto.
Qed.

End DFT_Rewriting_Rules.

End Merle_Algebra.
