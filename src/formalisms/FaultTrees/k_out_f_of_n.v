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
(* Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Oqarina.coq_utils.all.
(*| .. coq:: |*)

Section k_out_of_n.
(*|
k-out-of-N gate
===============

We provide a definition of the k-out-of-N gate for the boolean case, along with two simplification results.

|*)

Definition k_out_of_n_bool (k : nat) (l : list bool)  :=
    if Nat.leb k (count_occ bool_dec l true)
    then true else false.

Lemma k_out_of_N_OR: forall (l : list bool),
    k_out_of_n_bool 1 l = orbl l.
Proof.
    intros.
    unfold k_out_of_n_bool.
    induction l.
    - intuition.
    - destruct a.
        * rewrite count_occ_cons_eq.
            + simpl ; rewrite orbl_true ; reflexivity.
            + intuition.
        * rewrite count_occ_cons_neq.
            + rewrite orbl_false. apply IHl.
            + intuition.
Qed.

Lemma k_out_of_N_AND: forall (l : list bool),
        k_out_of_n_bool (List.length l) l = andbl l.
Proof.
    unfold k_out_of_n_bool. simpl.
    induction l.
    - intuition.
    - destruct a.
        * rewrite count_occ_cons_eq.
            + rewrite andbl_true. rewrite length_S.
              assert (Nat.leb (S (List.length l)) (S (count_occ bool_dec l true)) = Nat.leb (List.length l) (count_occ bool_dec l true)). intuition.
              apply IHl.
            + intuition.
        * rewrite count_occ_cons_neq.
            + intros. rewrite length_S.
              assert (Nat.leb (S (Datatypes.length l)) (count_occ bool_dec l true) = false).
              rewrite PeanoNat.Nat.leb_gt.
              generalize count_occ_bound ; auto with *. rewrite H. rewrite andbl_false ; reflexivity.
            + intuition.
Qed.

(*| .. coq:: none|*)
End k_out_of_n.
