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
(*| .. coq:: none |*)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListDec.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.

Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.AADL.Kernel.component.
(*| .. coq:: |*)

(*|
Features
--------

|*)

(*| Valid_Features_Category |*)

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

Definition Well_Formed_Features (l : list feature) :=
    Features_Identifiers_Are_Unique (l) /\
    Well_Formed_Feature_Ids l.

Lemma Well_Formed_Features_dec : forall l : list feature,
    { Well_Formed_Features l } + { ~ Well_Formed_Features l }.
Proof.
    prove_dec.
Qed.
