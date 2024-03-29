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
Require Import Lia.
(*| .. coq::  |*)

(*|
Natural numbers
===============

The following extends some results from Coq natural numbers and the :coq:`PeanoNat.Nat` module.

|*)

(*| .. coq:: none |*)
Section PeanoNat_Nat_Ext.
(*| .. coq:: |*)

(*|
.. index:: zero_or_succ_positive, CoqExt; zero_or_succ_positive

* :coq:`zero_or_succ_positive` is a variant of :coq:`PeanoNat.Nat.zero_or_succ` to simplify our proofs.

|*)

Lemma zero_or_succ_positive: forall n : nat,
    n > 0 -> exists m, n = S m.
Proof.
    intros.
    assert (n = 0 \/ exists m, n = S m).
    apply PeanoNat.Nat.zero_or_succ.
    destruct H0.
    contradict H. lia.
    trivial.
Qed.

(*|
.. index:: nat_split, CoqExt; nat_split

* :coq:`nat_plit` is a technical trivial lemma to split a natural number that is known to be higher than another.

|*)

Lemma nat_split: forall n m: nat,
    n > m -> exists p, n = m + p.
Proof.
    intros.
    exists (n - m) ; lia.
Qed.

Lemma nat_split2: forall n m:nat,
    exists p, n = m + p \/ m = n + p.
Proof.
    generalize Compare_dec.dec_le.

    intros.
    specialize (H n m).
    destruct H.
    - exists (m - n). lia.
    - exists (n - m). lia.
Qed.

(*| .. coq:: none |*)
End PeanoNat_Nat_Ext.
(*| .. coq::  |*)
