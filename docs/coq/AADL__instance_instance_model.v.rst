.. coq::


.. coq:: none

   (** Coq Library *)
   Require Import Coq.Logic.Decidable.
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Coq.Lists.ListDec.
   Require Import Coq.Bool.Sumbool.

   (** Oqarina library *)
   Require Import Oqarina.AADL.Kernel.all.
   Require Import Oqarina.AADL.legality.all.
   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.
   Require Import Oqarina.AADL.declarative.all.

Instance model
===============


In the previous chapter, we introduced a generic component model that matches the concepts of AADL component type, implementation and instances. In this chapter. we show how to specialize this model to support the AADL instance model.

AADL instance model
--------------------

* An AADL instance model is a well-formed generic AADL component.

.. coq:: none

   Section AADL_Instance.

.. coq::

   Definition Is_AADL_Instance (c : component) : Prop :=
       Well_Formed_Component_Hierarchy c.

   Lemma Is_AADL_Instance_dec :
       forall c : component, { Is_AADL_Instance c } +
                               { ~Is_AADL_Instance c }.
   Proof.
       unfold Is_AADL_Instance.
       intros.
       repeat apply dec_sumbool_and; auto.
   Defined.

   Definition Well_Formed_Component_Instance (c : component) :=
       Well_Formed_Component_Implementation c.

   Lemma Well_Formed_Component_Instance_dec :
       forall (c:component),
           { Well_Formed_Component_Instance c } +
           { ~Well_Formed_Component_Instance c }.
   Proof.
       intros.
       unfold Well_Formed_Component_Instance.
       apply Well_Formed_Component_Implementation_dec.
   Defined.

.. coq:: none

   End AADL_Instance.

The :coq:`prove_Is_AADL_Instance` tactic helps proving a component is a valid AADL instance

.. coq::

   Ltac prove_Is_AADL_Instance :=
       repeat match goal with
         | |- Is_AADL_Instance _ => compute; repeat split; auto
         | |- (_ =  EmptyString -> False) => intuition; inversion H
         | |- NoDup nil => apply NoDup_nil
         | |- NoDup  _  => apply NoDup_cons
         | |- ~ In _ _ => apply not_in_car
         | |- Id _ <> Id _ => apply identifier_string_neq; easy
         | |- ~ In _ [] => apply in_nil
       end.

   Ltac prove_Well_Formed_Component_Instance :=
       repeat match goal with
         | |- Well_Formed_Component_Instance _ => compute; repeat split; auto
         | |- (_ =  EmptyString -> False) => intuition; inversion H
         | |- NoDup nil => apply NoDup_nil
         | |- NoDup  _  => apply NoDup_cons
         | |- ~ In _ _ => apply not_in_cons
         | |- _ /\ _ => split
         | |- Id _ <> Id _ => apply identifier_string_neq; easy
         | |- ~ In _ [] => apply in_nil
       end.
