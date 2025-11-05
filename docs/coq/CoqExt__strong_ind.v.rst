.. coq::


.. coq:: none

   Require Import PeanoNat.
   Require Import Lia.

Strong Induction Principle
==========================

Coq generates general induction principles. In some cases, we need a strong induction princple that is introduced in this section.

.. coq:: none

   Section StrongInduction.

.. index:: strong induction, CoqExt; strong induction (tactic)

Let's assume we have a proposition indexed by a natural number and the stronger inductive hypothesis :coq:`IH`.

.. coq::

   Variable P : nat -> Prop.
   Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

A direct result is that :coq:`P (0)` always holds.

.. coq::

   Lemma P0 : P 0.
   Proof.
       apply IH; intros.
       inversion H.
   Qed.

We prove a strong hypothesis first, then the final result.

.. coq::

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

.. coq:: none

   End StrongInduction.

Here is the new strong induction principle we obtain:

.. coq::

   Check strong_induction.
   (* strong_induction
   	 : forall P : nat -> Prop,
          (forall m : nat, (forall n : nat, n < m -> P n) -> P m) ->
          forall n : nat, P n *)

We provide the tactic :coq:`strong induction` to use this new principle in our proofs.

.. coq::

   Tactic Notation "strong" "induction" ident(n) :=
       induction n using strong_induction.
