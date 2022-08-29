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

(* Oqarina Library *)
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.FaultTrees.AbstractFaultTree.

Section Fault_Tree_Bool.
(*| .. coq:: |*)

(*|

Boolean fault tree
==================

Stupid instantiation of the previous abstract fault tree. Basic events are simple booleans.

|*)

#[global]
Instance bool_Basic_Event_Operators : Basic_Event_Operators bool :=
{
   (* A_eq_dec := bool_dec ;*)
    T := true ;
    F := false ;

    b_AND := andb ;
    b_ANDl_singleton := andbl_singleton ;

    b_ANDl := andbl ;
    b_ANDl_concatenate := andbl_concatenate ;

    b_OR := orb ;

    b_ORl := orbl ;
    b_ORl_concatenate := orbl_concatenate ;

    (* For boolean fault tree, the following gates are not defined ‘*)

    b_PANDl := (fun x => None) ;
}.

Definition BFT := fault_tree bool.

(*| .. coq:: none |*)
End Fault_Tree_Bool.

Section Fault_Tree_Bool_Examples.
(*| .. coq::  |*)

(*| From these definitions, one can directly built a fault tree, check it is correct, and evaluate it. |*)

Example Basic_BFT : BFT :=
    in_tree (AND bool)
    [ in_tree (BASIC true) [] ;
      in_tree (BASIC false) []].

Fact Basic_BFT_OK : valid_static_fault_tree Basic_BFT.
Proof.
    prove_valid_fault_tree.
Qed.

Lemma Compute_Fault_Tree_Basic_BFT_OK:
    Compute_Fault_Tree'' Basic_BFT = Some false.
Proof.
    trivial.
Qed.

(*| .. coq:: none |*)
End Fault_Tree_Bool_Examples.

(*|
k-out-of-N gate
===============

We provide a definition of the k-out-of-N gate along with two simplification results.

|*)

Definition k_out_of_n_bool (k : nat) (l : list bool)  :=
    if Nat.leb k (count_occ bool_dec l T)
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

Lemma k_out_of_N_AND: forall (l : list bool) (n : nat),
        k_out_of_n_bool (List.length l) l = andbl l.
Proof.
    unfold k_out_of_n_bool. simpl.
    induction l.
    - intuition.
    - destruct a.
        * rewrite count_occ_cons_eq.
            + rewrite andbl_true. rewrite length_S.
              assert (Nat.leb (S (length l)) (S (count_occ bool_dec l true)) = Nat.leb (length l) (count_occ bool_dec l true)). intuition.
              apply IHl.
            + intuition.
        * rewrite count_occ_cons_neq.
            + intros. rewrite length_S.
              assert (Nat.leb (S (Datatypes.length l)) (count_occ bool_dec l true) = false).
              rewrite PeanoNat.Nat.leb_gt.
              generalize count_occ_bound ; intuition. rewrite H. rewrite andbl_false ; reflexivity.
            + intuition.
Qed.
