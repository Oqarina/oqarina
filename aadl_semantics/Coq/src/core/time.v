(** %\chapter{time.v -- Time type} %*)


(* begin hide *)
(** Coq Library *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
(* end hide *)

(** * AbstractTime

AbstractTime is an axiomatization of the notion of time, with elements 0 and 1, the addition operation and the relations %$<$% (less than or lt) %$\le$% (less or equal than, or lg) and equality. We assume %$\le$% is a total order relation. In addition, we assume only positive values for Time.

*)
Module Type AbstractTime.

    Parameter Time : Set.
    Parameter Zero: Time.
    Parameter One: Time.
    Parameter tle: Time -> Time -> Prop.
    Parameter tlt: Time -> Time -> Prop.
    Parameter tadd: Time -> Time -> Time.

    Notation "t1 @<= t2" := (tle t1 t2) (at level 70, no associativity).
    Notation "t1 @< t2" := (tlt t1 t2) (at level 70, no associativity).
    Notation "t1 @+ t2" := (tadd t1 t2) (at level 50, left associativity).

    Axiom tzerop: forall n, {n = Zero} + {Zero @< n}.
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

    NaturalTime is an implementation of the AbstractTime module. The proofs of all axioms is a consequence of Peano axiomatization provided by Coq.

*)

Module NaturalTime <: AbstractTime.

    Definition Time := nat.
    Definition Zero := 0.
    Definition One  := 1.
    Definition tle := le.
    Definition tlt := lt.
    Definition tadd:= plus.
    Notation "t1 @<= t2" := (tle t1 t2) (at level 70, no associativity).
    Notation "t1 @< t2" := (tlt t1 t2) (at level 70, no associativity).
    Notation "t1 @+ t2" := (tadd t1 t2) (at level 50, left associativity).

    Lemma tzerop: forall n, {n = Zero} + {Zero @< n}.
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
        unfold "@<=".  apply Nat.le_trans.
   Qed.

    Lemma tle_connexity: forall a b, { a @<= b } + { b @<= a }.
    Proof.
        unfold "@<=". apply le_ge_dec.
    Qed.

End NaturalTime.
