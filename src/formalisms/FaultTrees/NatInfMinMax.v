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

Require Export Coq.ZArith.Zmin.
Require Export Coq.ZArith.Zmax.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.Ndist.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Scheme Equality for natinf.

Definition ni_lt (d d':natinf) :=
  match d with
  | infty => False
  | ni n => match d' with
            | infty => True
            | ni n' => lt n n'
            end
  end.

Definition compare' (n m :natinf) : comparison :=
  match n, m with
    | infty, infty => Eq
    | _, infty => Lt
    | infty, _ => Gt
    | ni n', ni m' => Nat.compare n' m'
  end.

Lemma cmp_antisym (a b : natinf):
  compare' a b = CompOpp (compare' b a).
Proof.
  unfold compare';
  induction a ;
  induction b ; auto.
  apply Nat.compare_antisym.
Qed.

Lemma compare_helper_gt' (a b : natinf) : compare' a b = Lt ->
  compare' b a = Gt.
Proof.
  rewrite cmp_antisym.
  destruct (compare' b a) ; auto. discriminate.
Qed.

Lemma compare_helper_lt' (a b : natinf) : compare' a b = Gt ->
  compare' b a = Lt.
Proof.
  rewrite cmp_antisym.
  destruct (compare' b a) ; auto. discriminate.
Qed.

Lemma natinf_compare_eq: forall (n m : natinf),
  compare' n m = Eq -> n = m.
Proof.
  unfold compare'.
  simple induction n ; simple induction m.
  - auto.
  - discriminate.
  - discriminate.
  - intros. apply PeanoNat.Nat.compare_eq in H ; auto.
Qed.

Lemma natinf_compare_eq': forall (n m : natinf),
   n = m -> compare' n m = Eq.
Proof.
  intros.
  rewrite H.
  destruct m ; auto.
  simpl. apply Nat.compare_eq_iff ; auto.
Qed.

Lemma ni_min_assoc :
  forall d d' d'':natinf, ni_min (ni_min d d') d'' = ni_min d (ni_min d' d'').
 Proof.
   simple induction d; trivial. simple induction d'; trivial.
   simple induction d''; trivial.
   unfold ni_min. intro.
   enough (min (min n n0) n1 = min n (min n0 n1)) by (rewrite H; reflexivity).
   induction n in n0, n1 |- *; trivial.
   destruct n0; trivial. destruct n1; trivial.
   intros. simpl. auto.
 Qed.

 Lemma ni_min_assoc_r :
 forall d d' d'':natinf, ni_min d (ni_min d' d'')  = ni_min (ni_min d d') d''.
Proof.
  simple induction d; trivial. simple induction d'; trivial.
  simple induction d''; trivial.
  unfold ni_min. intro.
  enough (min (min n n0) n1 = min n (min n0 n1)) by (rewrite H; reflexivity).
  induction n in n0, n1 |- *; trivial.
  destruct n0; trivial. destruct n1; trivial.
  intros. simpl. auto.
Qed.

Section NatinfTotalOrder.

Lemma ni_min_case : forall d d':natinf,
  { ni_min d d' = d } + { ni_min d d' = d'}.
Proof.
  destruct d.
  - right. exact (ni_min_inf_l d').
  - destruct d'.
    + left. exact (ni_min_inf_r (ni n)).
    + unfold ni_min.
      enough ({min n n0 = n} + { min n n0 = n0}) as [-> | ->].
      * left. reflexivity.
      * right. reflexivity.
      * destruct (Nat.min_dec n n0); [left|right]; assumption.
Qed.

Lemma natinf_eq_le_def :
  forall x y, @eq natinf x y <-> ni_le x  y /\ ni_le y x.
Proof.
  intros.
  split.
  intros H; rewrite -> H.
  firstorder using ni_le_refl.
  firstorder using ni_le_antisym.
Qed.

Lemma ni_le_total : forall d d':natinf, { ni_le d d' } + { ni_le d' d}.
Proof.
  unfold ni_le. intros. rewrite (ni_min_comm d' d). apply ni_min_case.
Defined.

Definition ni_max (d d':natinf) :=
  match d with
  | infty => infty
  | ni n => match d' with
            | infty => infty
            | ni n' => ni (max n n')
            end
  end.

Lemma ni_max_split: forall (d d':natinf),
  ni_max d d' = infty \/ ni_max d d' = d \/ ni_max d d' = d'.
Proof.
  intros.
  unfold ni_max.
  destruct d.
  - left. trivial.
  - destruct d'.
    + left. trivial.
    + right.
      assert (H: max n n0 = n \/ max n n0 = n0).
      lia. destruct H ;  rewrite H; auto.
Qed.

Lemma ni_max_idemp : forall d:natinf, ni_max d d = d.
Proof.
  simple induction d; trivial.
  unfold ni_max.
  simple induction n; trivial.
  intros.
  simpl.
  inversion H.
  rewrite H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma ni_max_comm : forall d d':natinf, ni_max d d' = ni_max d' d.
Proof.
  simple induction d.
  - simple induction d'; trivial.
  - simple induction d'; trivial. elim n.
    + simple induction n0; trivial.
    + intros. elim n1; trivial. intros. unfold ni_max in H.
      enough (max n0 n2 = max n2 n0) by (unfold ni_max; simpl; rewrite H1; reflexivity).
      enough (ni (max n0 n2) = ni (max n2 n0)) by (inversion H1; trivial).
      exact (H n2).
Qed.

Lemma ni_max_assoc :
  forall d d' d'':natinf,
    ni_max (ni_max d d') d'' = ni_max d (ni_max d' d'').
Proof.
  simple induction d; trivial. simple induction d'; trivial.
  simple induction d''; trivial.
  unfold ni_max. intro.
  enough (max (max n n0) n1 = max n (max n0 n1)) by (rewrite H; reflexivity).
  induction n in n0, n1 |- *; trivial.
  destruct n0; trivial. destruct n1; trivial.
  intros. simpl. auto.
Qed.

Lemma ni_max_assoc_r :
  forall d d' d'':natinf,
    ni_max d (ni_max d' d'') = ni_max (ni_max d d') d''.
Proof.
  simple induction d; trivial. simple induction d'; trivial.
  simple induction d''; trivial.
  unfold ni_max. intro.
  enough (max (max n n0) n1 = max n (max n0 n1)) by (rewrite H; reflexivity).
  induction n in n0, n1 |- *; trivial.
  destruct n0; trivial. destruct n1; trivial.
  intros. simpl. auto.
Qed.

 Lemma ni_max_inf_l : forall d:natinf, ni_max infty d = infty.
 Proof.
  simple induction d; trivial.
  Qed.

 Lemma ni_max_inf_r : forall d:natinf, ni_max d infty = infty.
 Proof.
  simple induction d; trivial.
 Qed.

 Lemma ni_max_0_l : forall d:natinf, ni_max (ni 0) d = d.
 Proof.
  simple induction d; trivial.
  Qed.

 Lemma ni_max_0_r : forall d:natinf, ni_max d (ni 0) = d.
 Proof.
  intros.
  rewrite ni_max_comm.
  apply ni_max_0_l.
 Qed.

Lemma min_max_distrb:
 forall (n1 n2 n3: natinf),
     ni_min n1 (ni_max n2 n3) =
     ni_max (ni_min n1 n2) (ni_min n1 n3).
Proof.
  intros.
  destruct n1; auto.
  destruct n2; auto ; try rewrite ni_max_inf_l ; try rewrite ni_min_inf_r.
  destruct n3; auto.
  - rewrite ni_min_inf_r ; rewrite ni_max_idemp; trivial.
  - simpl. apply f_equal.  rewrite Nat.min_max_absorption ; reflexivity.
  - destruct n3. rewrite ni_max_inf_r. rewrite ni_min_inf_r.
    * simpl. apply f_equal. rewrite Nat.max_comm. rewrite Nat.min_max_absorption ; reflexivity.
    * simpl. apply f_equal. apply Nat.min_max_distr.
Qed.

Lemma max_min_distrb:
 forall (n1 n2 n3: natinf),
     ni_max n1 (ni_min n2 n3) =
     ni_min (ni_max n1 n2) (ni_max n1 n3).
Proof.
 intros.
 destruct n1; auto.
 destruct n2; auto ; try rewrite ni_max_inf_l ; try rewrite ni_min_inf_r.
 destruct n3; auto. simpl. apply f_equal. apply Nat.max_min_distr.
Qed.

Lemma ni_le_antisym : forall d d':natinf, ni_le d d' -> ni_le d' d -> d = d'.
Proof.
  unfold ni_le. intros d d'. rewrite ni_min_comm. intro H. rewrite H. trivial.
Qed.

Lemma ni_le_min1:
  forall x y : natinf, ni_le x y -> ni_min x y = x.
Proof.
  trivial.
Qed.

Lemma ni_le_min2:
  forall x y : natinf, ni_le y x -> ni_min x y = y.
Proof.
  intros. destruct x, y ; auto.
  apply ni_le_le in H.
  simpl.
  rewrite Nat.min_r ; auto.
Qed.

Lemma ni_le_min3:
  forall x y : natinf, ni_le y x -> ni_max x y = x.
Proof.
  intros. destruct x, y ; auto.
  apply ni_le_le in H.
  simpl.
  rewrite Nat.max_l ; auto.
Qed.

Lemma ni_le_min4:
  forall x y : natinf, ni_le x y -> ni_max x y = y.
Proof.
  intros. destruct x, y ; auto.
  apply ni_le_le in H.
  simpl.
  rewrite Nat.max_r ; auto.
Qed.

Lemma ni_max_max: forall x y : natinf, ni_max (ni_max x y) x = ni_max x y.
Proof.
  intros.
  unfold ni_max.
  destruct x, y ; intuition.
Qed.

End NatinfTotalOrder.
