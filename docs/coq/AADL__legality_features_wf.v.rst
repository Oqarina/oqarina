.. coq::


.. coq:: none

   (** Coq Library *)
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Coq.Bool.Bool.
   Require Import Coq.Lists.ListDec.

   (** Oqarina library *)
   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.

   Require Import Oqarina.AADL.Kernel.all.

Features
--------

Valid_Features_Category

.. coq::

   Fixpoint Valid_Features_Category
       (l : list feature)
       (lcat : list FeatureCategory)
   :=
       match l with
           | nil => True
           | h :: t => In (projectionFeatureCategory h) lcat /\
                       Valid_Features_Category t lcat
       end.

   Lemma Valid_Features_Category_dec :
       forall (l:list feature) (lcat :list FeatureCategory),
           { Valid_Features_Category l lcat } +
           { ~Valid_Features_Category l lcat }.
   Proof.
       prove_dec.
       induction l.
       auto.
       apply dec_sumbool_and.
       - apply In_dec; apply FeatureCategory_eq_dec.
       - auto.
   Qed.

   (** XXX Actually wrong, we must check for the direction of the feature as well *)

   Definition Well_Formed_Component_Interface
       (c: component) (l : list FeatureCategory) :=
           Valid_Features_Category (c->features) l.

   Lemma Well_Formed_Component_Interface_dec :
       forall (c:component) (lcat :list FeatureCategory),
           {Well_Formed_Component_Interface c lcat} +
           { ~Well_Formed_Component_Interface c lcat}.
   Proof.
       prove_dec.
       apply Valid_Features_Category_dec.
   Qed.

   Definition Well_Formed_Feature_Id (f : feature) : Prop :=
     (Well_Formed_Identifier_prop (projectionFeatureIdentifier f)).

   Lemma Well_Formed_Feature_Id_dec : forall f : feature,
     {Well_Formed_Feature_Id f } + {~Well_Formed_Feature_Id f }.
   Proof.
       prove_dec.
   Qed.

   Definition Well_Formed_Feature_Ids (l : list feature) : Prop :=
       All Well_Formed_Feature_Id l.

   Lemma Well_Formed_Feature_Ids_dec : forall l : list feature,
       { Well_Formed_Feature_Ids l } + { ~Well_Formed_Feature_Ids l }.
   Proof.
       prove_dec.
   Qed.

   Definition Features_Identifiers_Are_Unique (l : list feature) : Prop :=
       (NoDup (Features_Identifiers l)).

   Lemma Features_Identifiers_Are_Unique_dec :
       forall l : list feature,
           { Features_Identifiers_Are_Unique l } + { ~ Features_Identifiers_Are_Unique l }.
   Proof.
       prove_dec.
   Qed.

We combine the previous results to build the :coq:`Well_Formed_Features` predicate.

.. coq::

   Definition Well_Formed_Features (l : list feature) :=
       Features_Identifiers_Are_Unique (l) /\
       Well_Formed_Feature_Ids l.

   Lemma Well_Formed_Features_dec : forall l : list feature,
       { Well_Formed_Features l } + { ~ Well_Formed_Features l }.
   Proof.
       prove_dec.
   Qed.

The following are technical lemmas.

.. coq::

   Lemma Well_Formed_Features_cons: forall a l,
       Well_Formed_Features (a::l)
       -> Well_Formed_Features [a] /\ Well_Formed_Features l.
   Proof.
       unfold Well_Formed_Features.
       unfold Features_Identifiers_Are_Unique.
       simpl.
       intros.
       destruct H.
       apply NoDup_cons_iff in H.
       intuition.
       prove_NoDup_singleton.
   Qed.

   Lemma Well_Formed_Features_in_resolve: forall l x,
       Well_Formed_Features l
           -> In x l
           -> Get_Element_By_Name _ l (x->id) = Some x.
   Proof.
       intros l.
       induction l.
       - intros. inversion H0.
       - intros. destruct H0.
         + simpl. rewrite H0. rewrite identifier_eqb_refl. reflexivity.
         +
           (* This part of the proof has some technicalities.
           Get_Feature_By_Name compare id. We first show that a and x have different id, then conclude. *)
           assert (a->id <> (x->id)).
           unfold Well_Formed_Features in H. destruct H.
           unfold Features_Identifiers_Are_Unique in H.
           unfold Features_Identifiers in H.
           simpl in H.
           apply NoDup_cons_iff in H.
           destruct H.
           assert (In (x->id)
                       (map (fun y => projectionFeatureIdentifier y) l)).
           apply in_map. apply H0.
           eapply not_in_in.
           apply H.
           apply H3.

           (* We use the previous assertions to conclude. *)
           simpl.
           apply identifier_beq_neq in H1.
           simpl in H1.
           rewrite H1.

           apply Well_Formed_Features_cons in H.
           apply IHl ; intuition.
   Qed.
