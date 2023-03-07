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
Require Import PeanoNat.
Require Import Lia.
(*| .. coq:: |*)

(*|
Strong Induction Principle
==========================
|*)

(*| .. coq:: none |*)
Section StrongInduction.
(*| .. coq:: |*)

(*| Let's assume we have a proposition indexed by a natural number and the stronger inductive hypothesis. |*)

Variable P : nat -> Prop.
Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

(*| A direct result is that :coq:`P (0)` holds. |*)

Lemma P0 : P 0.
Proof.
    apply IH; intros.
    inversion H.
Qed.

(*| We prove a strong hypothesis first, then the final result. |*)

Lemma strong_induction_leq : forall n,
    (forall m, m <= n -> P m).
Proof.
    induction n ; intros.
    - inversion H. apply P0.
    - inversion H.
        + apply IH. intros. apply le_S_n in H1. apply IHn. apply H1.
        + apply IHn. apply H1.
Qed.

Theorem strong_induction : forall n, P n.
Proof.
    intros.
    induction n.
    - apply P0.
    - apply IH. intros.
      apply le_S_n in H.
      eapply strong_induction_leq.
      apply H.
  Qed.

(*| .. coq:: none |*)
End StrongInduction.
(*| .. coq:: |*)

(*| Here is the new strong induction principle we obtain: |*)

Check strong_induction.
(* strong_induction
	 : forall P : nat -> Prop,
       (forall m : nat, (forall n : nat, n < m -> P n) -> P m) ->
       forall n : nat, P n *)

(*| We provide the tactic :coq:`strong induction` to use this new principle. |*)

Tactic Notation "strong" "induction" ident(n) :=
    induction n using strong_induction.
