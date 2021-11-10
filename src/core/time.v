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

(** XXX As an exercise, do the same for Decimal, or a similar type. *)

Require Import Compare_dec.
Require Import OrderedType.

Section s.
Variable X : Set.
Variable P : X -> Prop.

Lemma foo: (exists x, ~P x) -> ~(forall x, P x).
Proof.
  intros. intro.
  destruct H.
  apply H.
  apply H0.
Qed.

End s.


(* In the following, we capture the definition of simulation time as presented in

    J. Nutaro, “Toward a Theory of Superdense Time in Simulation Models,” ACM Trans. Model. Comput. Simul., vol. 30, no. 3, pp. 1–13, Jul. 2020, doi: 10.1145/3379489.

Let [t] a type with the usual defintions for +, −, >, 1, and 0. In other words, [t] is both an ordered type and a number type. In the following, we build [SimulationTime] as an extension of an [UsualOrderedType] to also benefit from results on equality. *)

Require Import Coq.Structures.OrderedTypeEx.

Module Type SimulationTime (Import O : UsualOrderedType).

    Parameter plus: t -> t -> t.
    Parameter minus: t -> t -> t.
    Parameter succ: t -> t.

    (* P1 There exists 0 such that, for all t , t + 0 = 0 + t = t. Due to *)

    Parameter Zero: t.
    Axiom P1 : forall tv:t, plus Zero tv = tv .
    Axiom P1bis: forall tv : t, {tv = Zero} + {lt Zero tv}.

    (* P2 If h1 < h2 then t + h1 < t + h2 *)
    Axiom P2: forall tv h1 h2: t, lt h1 h2 -> lt (plus h1 tv) (plus h2 tv).

    (* P3 If h1 ≥ 0 and h2 ≥ 0 then (t + h1) + h2 = t + (h1 + h2) *)
    Axiom P3: forall tv h1 h2: t, plus (plus tv h1) h2 = plus tv (plus h1 h2).

    (* P4 If t1 < t2 then there exists h > 0 such that t1 + h = t2 *)
    Axiom P4: forall t1 t2: t, lt t1 t2 -> exists h: t, plus t1 h = t2.

    (* P5 There is a successor function S(t) such that the interval [t,S(t))
       contains exactly t. *)
    Parameter One: t.
    Axiom P5: forall t, minus (succ t) t = One.

    (* Proposition 1. The number 0 is unique. *)

    Lemma Proposition_1'': forall tv h:t, lt Zero h -> plus h tv = tv -> False.
    Proof.
        intros tv h H1 H2.

        enough (H3 : lt Zero h -> lt (plus Zero tv) (plus h tv)).
        - rewrite H2 in H3.
          rewrite P1 in H3.
          apply lt_not_eq in H3.
          contradict H3. apply eq_refl. auto.
        - apply P2.
    Defined.

    Lemma Proposition_1: forall tv h: t,
         (h = Zero -> plus h tv = tv) /\ (lt Zero h -> plus h tv = tv -> False).
    Proof.
        intros.
        split.
        - intros. subst. apply P1.
        - apply Proposition_1''.
    Defined.

End SimulationTime.

Module NatSimulationTime <: SimulationTime (Nat_as_OT).
    Import Nat_as_OT.


    Definition plus := plus.
    Definition minus := minus.
    Definition Zero := 0.

    Lemma P1: forall tv:t, plus Zero tv = tv.
    Proof.
        intros.
        unfold Zero. unfold plus.
        lia.
    Qed.

    Lemma P1bis: forall tv : t, {tv = Zero} + {lt Zero tv}.
    Proof.
        unfold Zero. unfold lt.
        apply zerop. (* forall n : nat, {n = 0} + {0 < n} *)
    Qed.

   Lemma P2: forall tv h1 h2: t, lt h1 h2 -> lt (plus h1 tv) (plus h2 tv).
   Proof.
       unfold lt. unfold plus. intuition.
   Qed.

    Lemma P3: forall tv h1 h2: t, plus (plus tv h1) h2 = plus tv (plus h1 h2).
    Proof.
        unfold plus. intuition.
    Qed.

    Lemma P4: forall t1 t2: t, lt t1 t2 -> exists h: t, plus t1 h = t2.
    Proof.
        (* Generic part of the proof *)
        intros.
        apply ex_intro with (minus t2 t1).

        (* This part assumes we use natural number *)
        unfold plus. unfold lt in *. unfold minus.
        lia.
    Qed.

    Definition succ := S.
    Definition One:= 1.
    Lemma P5: forall t, minus (succ t) t = One.
    Proof.
        intros.
        unfold minus. unfold succ. unfold One.
        lia.
    Qed.

    (* XXX It should not be required to copy this, investigate Coq modules *)
    Lemma Proposition_1'': forall tv h:t, lt Zero h -> plus h tv = tv -> False.
    Proof.
        intros tv h H1 H2.

        enough (H3 : lt Zero h -> lt (plus Zero tv) (plus h tv)).
        - rewrite H2 in H3.
          rewrite P1 in H3.
          apply lt_not_eq in H3.
          contradict H3. apply eq_refl. auto.
        - apply P2.
    Defined.

    Lemma Proposition_1: forall tv h: t,
         (h = Zero -> plus h tv = tv) /\ (lt Zero h -> plus h tv = tv -> False).
    Proof.
        intros.
        split.
        - intros. subst. apply P1.
        - apply Proposition_1''.
    Defined.

End NatSimulationTime.
