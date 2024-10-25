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
(* From https://www.cs.cornell.edu/courses/cs4160/2020sp/sf/vfa/full/ADT.html

*)
From mathcomp Require Import finset fintype ssrbool eqtype.
Require Import Coq.Bool.Bool.
Require Import Oqarina.CoqExt.finset_Ext.

Ltac trivialize :=
    repeat match goal with
    | [ H: _ |- ?x = ?x ] => reflexivity
    end.

Ltac my_tauto :=
    repeat match goal with
        | [ |- True ] => constructor
        | [ |- is_true true ] => constructor (* true is a coercion ..n*)

        | [ H : ?P |- ?P ] => exact H
        | [ H: _ |- ?x = ?x ] => reflexivity

        | [ |- _ /\ _ ] => constructor ; my_tauto
        | [ |- _ -> _ ] => intro ; my_tauto

        | [ H : false |- _ ] => inversion H
        | [ H : False |- _ ] => destruct H

        | [ H : _ /\ _ |- _ ] => destruct H ; my_tauto
        | [ H : _ \/ _ |- _ ] => destruct H ; my_tauto

        | [ H1 : ?P -> ?Q, H2 : ?P  |- _ ] => specialize (H1 H2)
        | [ H1 : ?P , H2 : ?P -> ?Q |- _ ] => specialize (H1 H2)
        | [ H : is_true ?P  |- if ?P then _ else _ ] => rewrite H

        | [ H : ?x = ?y |- _ ] => try subst
        | [ H1 : true, H2 : false |- _ ] => intuition

        | [ |- ?x ] => try (is_constructor x ; constructor)
    end.

Ltac split_goals :=
    repeat match goal with
    | [ H: _ |- _ /\ _ ] => split ; my_tauto ; split_goals
    | [ H: _ |- _ <-> _ ] => split ; my_tauto ; split_goals
    end.

Ltac intro_step :=
    repeat match goal with
    | [ |- forall x : ?T, _ ] => intros ; split_goals
    | [ |-  _ -> _ ] => intros ; split_goals

    end.

Ltac intro_proof :=
    intro_step ; simpl.

Ltac repeat_destruct Hyp :=
    let HypName := fresh Hyp in
    destruct Hyp as [HypName Hyp] ; try repeat_destruct Hyp.

Ltac unfold_destruct X H :=
    unfold X in H.

Ltac destruct_if :=
    let name := fresh "if0" in
    repeat match goal with
    | [ |- if ?x then _ else _ ] => destruct x eqn:name
    end.

Ltac try_subst :=
    repeat match goal with
        | [ H: ?x = ?y |- _ ] => subst
        | [ H: true |- _ ] => clear H
    end.

Ltac smart_destruct_rec H :=
    match type of H with
        | _ /\ _ =>
            let L := fresh "L" in
            let R := fresh "R" in
            destruct H as [L R]; smart_destruct_rec L; smart_destruct_rec R

        | _ \/ _ =>
            destruct H ; smart_destruct_rec H

        | if ?x then _ else _ =>
            let name := fresh "if0" in destruct x eqn:name ; smart_destruct_rec H

        | exists2 _, _ & _ =>
            let L := fresh "L" in
            let R := fresh "R" in
            destruct H as [L R]; smart_destruct_rec L; smart_destruct_rec R

        | _ => idtac
        end.

Ltac smart_destruct H :=
    smart_destruct_rec H ; try_subst ; my_tauto.

Ltac simplify_finset :=
    try rewrite in_set0 in * ;
    try rewrite setUA in * ;
    try repeat rewrite setU0 in *;
    try repeat rewrite set0U in *;
    try repeat rewrite in_set0 in *;
    try apply disjoint_set0 ; my_tauto.

Ltac smart_unfold Hyp :=
    match type of Hyp with
        | ?F _ _ _ => unfold F in Hyp
    end.

Ltac rewrite_in_setU :=
    repeat rewrite in_setU in * ;

    repeat match goal with
    | [ H : _ || _ |- _ ] => apply orb_true_iff in H
    end.

Ltac contradiction_in_H H1 H2 :=
    rewrite H1 in H2 ; inversion H2.
