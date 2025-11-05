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
   Require Import Oqarina.AADL.property_sets.all.
   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.

Declarative model
=================

In the previous chapter, we introduced a generic component model that matches the concepts of AADL component type, implementation and instances. In this chapter. we show how to specialize this model to support the AADL declarative model

Note: the following concepts of AADL are excluded: arrays, modes, flows.

In this chapter, we refine an AADL generic component into either a component type or a component implementation. We then introduce the concept of AADL packages as a collection of components, and AADL model has a collection of packages.

AADL Component Type
-------------------

* An AADL component type is a well-formed generic AADL component without subcomponents and connections.

.. coq:: none

   Section AADL_Component_Type.

.. coq::

   Definition Is_AADL_Component_Type_classifier (c : component) : Prop :=
       match c->classifier with
           | FQN _  _ s => match s with
                           | None => True
                           | Some _ => False
                           end
       end.

   Definition Is_AADL_Component_Type (c : component) : Prop :=
       Is_AADL_Component_Type_classifier c /\
       Well_Formed_Component_Hierarchy c /\
       c->subcomps = nil /\
       c->connections = nil.

   Lemma Is_AADL_Component_Type_dec :
       forall c : component, { Is_AADL_Component_Type c } +
                               { ~Is_AADL_Component_Type c }.
   Proof.
       prove_dec.
   Defined.

An AADL component type is well-formed iff. its features match some restrictions imposed by its category, and it is itself a well-formed component.

.. coq::

   Hint Resolve Is_AADL_Component_Type_dec : well_know_wf_dec.

   Definition Well_Formed_Component_Type (c: component) :=
           Is_AADL_Component_Type c /\
           Well_Formed_Component_Type_Interface c /\
           Well_Formed_Component c /\
           Well_Formed_Property_Associations c AADL_Predeclared_Property_Sets.

   Lemma Well_Formed_Component_Type_dec :
       forall (c:component),
           {Well_Formed_Component_Type c} +
           { ~Well_Formed_Component_Type c}.
   Proof.
       prove_dec.
   Defined.

.. coq:: none

   End AADL_Component_Type.

AADL Component Implementation
-----------------------------

An AADL component implementation is a well-formed generic AADL component.

.. coq:: none

   Section AADL_Component_Implementation.

.. coq::

   Definition Is_AADL_Component_Implementation_classifier (c : component) : Prop :=
       match c->classifier with
           | FQN _  _ s => match s with
                           | None => False
                           | Some _ => True
                           end
       end.

   Definition Is_AADL_Component_Implementation (c : component) : Prop :=
       Is_AADL_Component_Implementation_classifier c /\
       Well_Formed_Component_Hierarchy c.

   Lemma Is_AADL_Component_Implementation_dec :
       forall c : component, { Is_AADL_Component_Implementation c } +
                               { ~Is_AADL_Component_Implementation c}.
   Proof.
       prove_dec.
   Defined.

An AADL component implementation is well-formed iff. its subcomponents match some restrictions imposed by its category.

.. coq::

   Definition Well_Formed_Component_Implementation' (c: component) :=
       Is_AADL_Component_Implementation c /\
       Well_Formed_Component_Implementation_Subcomponents c /\
       Well_Formed_Component c /\
       Well_Formed_Property_Associations c AADL_Predeclared_Property_Sets /\
       Well_Formed_Property_Values'' c.

   Lemma Well_Formed_Component_Implementation'_dec :
   forall (c:component),
       {Well_Formed_Component_Implementation' c} +
       { ~Well_Formed_Component_Implementation' c}.
   Proof.
       prove_dec.
   Defined.

   Definition Well_Formed_Component_Implementation (c: component) :=
       Unfold_Apply Well_Formed_Component_Implementation' c.

   Lemma Well_Formed_Component_Implementation_dec :
       forall (c:component),
           {Well_Formed_Component_Implementation c} +
           { ~Well_Formed_Component_Implementation c}.
   Proof.
       prove_dec.
   Qed.

.. coq:: none

   End AADL_Component_Implementation.

.. coq::

   Lemma AADL_Component_Has_Well_Formed_Features:
       forall c, Is_AADL_Component_Type c \/
           Is_AADL_Component_Implementation c
           -> Well_Formed_Features (c ->features).
   Proof.
       intros.
       unfold Is_AADL_Component_Type in H.
       unfold Is_AADL_Component_Implementation in H.
       unfold Well_Formed_Component_Hierarchy in H.
       unfold Unfold_Apply in H.
       simpl in H.
       intuition.

       - assert (Unfold c = [c]).
         unfold Unfold.
         destruct c.
         rewrite H1. reflexivity.

         rewrite H2 in H0. simpl in H0. destruct H0.
         unfold Well_Formed_Component in H0.
         intuition.

       - destruct c.
         induction l0, l2.
         + simpl in *. unfold Well_Formed_Component in H1. intuition.
         + simpl in *. unfold Well_Formed_Component in H1. intuition.
         + simpl in *. intuition. apply H3.
           * unfold Well_Formed_Component in *. intuition.
             apply Well_Formed_Subcomponents_cons in H7.
             simpl. intuition.
           * apply All_app in H2. intuition.
         + simpl in *.
           unfold Well_Formed_Component in *. intuition.
   Qed.

AADL package
------------

An AADL package is a named-list of AADL components.

.. coq:: none

   Section AADL_Package.

An AADL package is well-formed iff its identifier is well-formed and its components are also well-formed.

.. coq::

   Definition Well_Formed_Package (p : package) :=
       Well_Formed_Identifier_prop (p->id) /\
       All (fun x => Well_Formed_Component_Type x \/
                       Well_Formed_Component_Implementation x)
           (p->components).

   Lemma Well_Formed_Package_dec :
       forall p : package, { Well_Formed_Package p } + { ~Well_Formed_Package p }.
   Proof.
       prove_dec.
   Qed.

.. coq:: none

   End AADL_Package.

.. coq::

   Ltac prove_Well_Formed_Package_inner :=
       repeat match goal with
           | |- _ /\ _ => repeat split ; auto
           | |- False => fail 2
           | |- (_ =  EmptyString -> False) => intuition; inversion H
           | |- NoDup nil => apply NoDup_nil
           | |- NoDup  _  => apply NoDup_cons
           | |- ~ In _ _ => apply not_in_car
           | |- Id _ <> Id _ => apply identifier_string_neq; easy
           | |- ~ In _ [] => apply in_nil
           | |- _ \/ _ => left ; repeat split; auto
           | |- _ \/ _ => right ; repeat split; auto
       end.

   Ltac prove_Well_Formed_Package :=
       repeat match goal with
           | |- Well_Formed_Package _ => compute ; repeat split
           | |- _ \/ _ => left ; prove_Well_Formed_Package_inner
           | |- _ \/ _ => right ; prove_Well_Formed_Package_inner
           | |- _ => prove_Well_Formed_Package_inner
       end.

At this stage, we simply have collection of well-formed packages. But this is not enough to guarantee the model is correct. We need to add some typing rules that assess all elements are properly resolved. This is addressed in the next sections.

AADL model as transitive closure
--------------------------------

So far, we have defined fragments of AADL: component types, implementations and packages. We now define an AADL model as a collection of AADL packages.

* An AADL model is a list of AADL packages.

.. coq:: none

   Section AADL_Model.

.. coq::

   Definition AADL_Model := list package.

   Definition Well_AADL_Model (m : AADL_Model) :=
       All Well_Formed_Package m.

   Lemma Well_AADL_Model_dec : forall m : AADL_Model,
       { Well_AADL_Model m } + { ~ Well_AADL_Model m }.
   Proof.
       prove_dec.
   Qed.

.. coq:: none

   End AADL_Model.
