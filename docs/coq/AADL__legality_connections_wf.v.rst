.. coq::

   (** %\chapter{Well-formedness rules of an AADL model}\label{chap::aadl_wf}% *)

.. coq:: none

   (** Coq Library *)
   Require Import Coq.Logic.Decidable.
   Require Import List.
   Import ListNotations. (* from List *)
   Set Implicit Arguments.
   Set Strict Implicit.

   (** Oqarina library *)
   Require Import Oqarina.AADL.Kernel.all.
   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.

Connections
-----------

.. coq::

   Definition Connections_Unique_Id (l : list connection) : Prop :=
       NoDup (Elements_Identifiers _ l).

   Lemma Connections_Unique_Id_dec :
       forall l : list connection,
       { Connections_Unique_Id l } + { ~ Connections_Unique_Id l }.
   Proof.
       prove_dec.
   Qed.

   Definition Get_Feature_By_Name' (s : identifier) (c : component) :=
       Get_Element_By_Name _ (c->features) s.

   Definition Get_Feature_By_Name (f : feature_ref) (c: component) :=
       match f with
       | FREF EmptyString s => Get_Feature_By_Name' (Id s) c
       | FREF s1 s2 =>
           let c1 := Get_Element_By_Name _ (c->subcomps) (Id s1) in
           match c1 with
           | None => None
           | Some c2 => Get_Feature_By_Name' (Id s2) c2
           end
       end.

   Definition Compatible_Direction_Features (f1 f2: feature) : Prop :=
       Is_Output_Port f1 = true /\ Is_Input_Port f2 = true.

   Definition Compatible_Category_Features (f1 f2: feature) : Prop :=
       let cat_f1 := projectionFeatureCategory f1 in
       let cat_f2 := projectionFeatureCategory f2 in
       cat_f1 = cat_f2. (* XXX *)

   Definition Compatible_Features (f1 f2 : feature) :=
       Compatible_Category_Features f1 f2 /\
       Compatible_Direction_Features f1 f2.

   Lemma Compatible_Features_dec : forall f1 f2,
       { Compatible_Features f1 f2 } + { ~ Compatible_Features f1 f2 }.
   Proof.
       prove_dec.
   Qed.

   Definition Well_Formed_Connection' (c : connection) (comp : component) :=
       let f1 := Get_Feature_By_Name (c ->src) comp in
       let f2 := Get_Feature_By_Name (c ->dest) comp in
       match (f1, f2) with
           | (None, _) => False
           | (_, None) => False
           | (Some f1', Some f2') => Compatible_Features f1' f2'
       end.

   Definition Well_Formed_Connection_list (c : component) :=
       All (fun x => Well_Formed_Connection' x c) (c->connections).

   Lemma Well_Formed_Connection_list_dec: forall c,
       { Well_Formed_Connection_list c } +
           { ~ Well_Formed_Connection_list c}.
   Proof.
       prove_dec.
   Qed.

   Definition Well_Formed_Connections (c : component) : Prop :=
       Connections_Unique_Id (c->connections) /\
       Well_Formed_Connection_list c.

   Lemma Well_Formed_Connections_dec: forall l,
       { Well_Formed_Connections l } + { ~ Well_Formed_Connections l }.
   Proof.
       prove_dec.
   Qed.

   Import AADL_Notations.
   Open Scope aadl_scope.

   Example A_Process :=
       process: "a_process" ->| "pack::a_process_classifier.impl"
       extends: None
       features: nil
       subcomponents: [
           thread: "producer" ->| "pack::producer.impl"
           extends: None
           features: [
               feature: out_event "a_feature"
             ]
           subcomponents: nil
           connections: nil
           properties: nil ;

           thread: "consumer" ->| "pack::consumer.impl"
           extends: None
           features: [
               feature: in_event "a_feature"
             ]
           subcomponents: nil
           connections: nil
           properties: nil
       ]
       connections: [
           connection: "c1" # "producer.a_feature" --> "consumer.a_feature"
       ]
       properties: nil.

   Ltac oq_generic_prove fn :=
       repeat match goal with
           | |- fn _ => compute; repeat split; auto
           | |- (_ =  EmptyString -> False) => intuition; inversion H
           | |- NoDup nil => apply NoDup_nil
           | |- NoDup  _  => apply NoDup_cons
           | |- ~ In _ _ => apply not_in_cons
           | |- _ /\ _ => split
           | |- Id _ <> Id _ => apply identifier_string_neq; easy
           | |- ~ In _ [] => apply in_nil
       end.
   (*
   Lemma A_Process_OK: Well_Formed_Component_Hierarchy A_Process.
   Proof.
       oq_generic_prove Well_Formed_Component_Hierarchy.
   Qed.
   *)
   Lemma t : Well_Formed_Connections A_Process.
   Proof.
       oq_generic_prove Well_Formed_Connections.
   Qed.
