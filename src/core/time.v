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
(** %\chapter{time.v -- Time type} %*)

(* begin hide *)
(** Coq Library *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Coq.NArith.Ndist.
(* end hide *)

(** * AbstractTime

    [AbstractTime] is an axiomatization of the notion of time, with elements [0] and [1], the plusition operation and the relations %$<$% (less than or lt) %$\le$% (less or equal than, or le) and equality. We assume %$\le$% is a total order relation. In plusition, we assume only positive values for time.

*)

Module Type AbstractTime.

    Parameter Time : Set.
    Parameter Zero: Time.
    Parameter One: Time.
    Parameter tle: Time -> Time -> Prop.
    Parameter tlt: Time -> Time -> Prop.
    Parameter tplus: Time -> Time -> Time.

    Notation "t1 @<= t2" := (tle t1 t2) (at level 70, no associativity).
    Notation "t1 @< t2" := (tlt t1 t2) (at level 70, no associativity).
    Notation "t1 @+ t2" := (tplus t1 t2) (at level 50, left associativity).

    Axiom tzerop: forall t : Time, {t = Zero} + {Zero @< t}.
    Axiom Time_eq_dec: forall x y : Time, {x=y}+{x<>y}.

    (** Axioms for total order:

        - Antisymmetry: If %$a\leq b$% and %$b\leq a$% then %$a=b$%;
        - Transitivity: If %$a\leq b$% and %$b\leq c$% then %$a\leq c$%;
        - Connexity: %$a\leq b$% or %$b\leq a$%

    *)

    Axiom tle_anti: forall a b, a @<= b -> b @<= a -> a = b.
    Axiom tle_trans: forall n m p, n @<= m -> m @<= p -> n @<= p.
    Axiom tle_connexity: forall a b, { a @<= b } + { b @<= a }.

End AbstractTime.

(** * NaturalTime

    [NaturalTime] is an implementation of the [AbstractTime] module. The proofs of all axioms is a consequence of the Peano'a axiomatization of natural numbers provided by Coq.

*)

Module NaturalTime <: AbstractTime.

    Definition Time := nat.
    Definition Zero := 0.
    Definition One  := 1.
    Definition tle := le.
    Definition tlt := lt.
    Definition tplus:= plus.
    Notation "t1 @<= t2" := (tle t1 t2) (at level 70, no associativity).
    Notation "t1 @< t2" := (tlt t1 t2) (at level 70, no associativity).
    Notation "t1 @+ t2" := (tplus t1 t2) (at level 50, left associativity).

    Lemma tzerop: forall t : Time, {t = Zero} + {Zero @< t}.
    Proof.
        unfold Zero. unfold "@<".
        apply zerop.
    Qed.

    Lemma Time_eq_dec: forall x y : Time, {x=y}+{x<>y}.
    Proof.
        unfold Time. apply Nat.eq_dec.
    Qed.

    Lemma tle_anti: forall a b, a @<= b -> b @<= a -> a = b.
    Proof.
        unfold "@<=". intros. intuition.
    Qed.

    Lemma tle_trans: forall n m p, n @<= m -> m @<= p -> n @<= p.
    Proof.
        unfold "@<=". apply Nat.le_trans.
   Qed.

    Lemma tle_connexity: forall a b, { a @<= b } + { b @<= a }.
    Proof.
        unfold "@<=". apply le_ge_dec.
    Qed.

End NaturalTime.

Module NaturalInfTime <: AbstractTime.

    Definition Time := natinf.
    Scheme Equality for natinf.
    
    Definition Zero := ni 0.
    Definition One  := ni 1.
    Definition tle := ni_le.
    Definition tlt :=
        fun t1 t2 => match t1 with
                    | infty => match t2 with
                                | infty => True
                                | ni _ => False
                                end
                    | ni n1 => match t2 with
                                | infty => True
                                | ni n2 => lt n1 n2
                                end
        end.

    Definition tplus :=
        fun t1 t2 => match t1 with
                    | infty => infty
                    | ni n1 => match t2 with
                                | infty => infty
                                | ni n2 => ni (n1 + n2)
                                end
        end.

    Notation "t1 @<= t2" := (tle t1 t2) (at level 70, no associativity).
    Notation "t1 @< t2" := (tlt t1 t2) (at level 70, no associativity).
    Notation "t1 @+ t2" := (tplus t1 t2) (at level 50, left associativity).

    Lemma tzerop: forall t : Time, {t = Zero} + {Zero @< t}.
    Proof.
        unfold Zero. unfold "@<".
        destruct t.
        - right. auto.
        - destruct n.
            * left. auto.
            * right. intuition.
    Qed.

    Lemma Time_eq_dec: forall x y : Time, {x=y}+{x<>y}.
    Proof.
        repeat decide equality.
    Qed.

    Lemma tle_anti: forall a b, a @<= b -> b @<= a -> a = b.
    Proof.
        unfold "@<=". apply ni_le_antisym.
    Qed.

    Lemma tle_trans: forall n m p, n @<= m -> m @<= p -> n @<= p.
    Proof.
        unfold "@<=". apply ni_le_trans.
   Qed.

   Lemma ni_min_case_sumbool : forall d d':natinf,
        {ni_min d d' = d} + {ni_min d d' = d'}.
   Proof.
     destruct d. right. exact (ni_min_inf_l d').
     destruct d'. left. exact (ni_min_inf_r (ni n)).
     unfold ni_min.
     enough ({min n n0 = n} + {min n n0 = n0}) as [-> | ->].
     left. reflexivity.
     right. reflexivity.
     destruct (Nat.min_dec n n0); [left|right]; assumption.
   Qed.

    Lemma tle_connexity: forall a b, { a @<= b } + { b @<= a }.
    Proof.
        unfold "@<=". unfold ni_le.
        intros.
        rewrite (ni_min_comm b a).
        apply ni_min_case_sumbool.
    Qed.

End NaturalInfTime.
