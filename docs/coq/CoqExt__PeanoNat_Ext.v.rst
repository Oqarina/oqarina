.. coq::


.. coq:: none

   Require Import Lia.

Natural numbers
===============

The following extends some results from Coq natural numbers and the :coq:`PeanoNat.Nat` module.

.. coq:: none

   Section PeanoNat_Nat_Ext.

.. index:: zero_or_succ_positive, CoqExt; zero_or_succ_positive

* :coq:`zero_or_succ_positive` is a variant of :coq:`PeanoNat.Nat.zero_or_succ` to simplify our proofs.

.. coq::

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

.. index:: nat_split, CoqExt; nat_split

* :coq:`nat_plit` is a technical trivial lemma to split a natural number that is known to be higher than another.

.. coq::

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

.. coq:: none

   End PeanoNat_Nat_Ext.
