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
Require Import Coq.Lists.ListDec.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Relations.Relation_Definitions.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.AADL.Kernel.component.
Require Import Oqarina.AADL.Kernel.properties.
Require Import Oqarina.AADL.Kernel.typecheck.
Require Import Oqarina.AADL.Kernel.features_helper.

Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section Helper_Functions.
(*| .. coq:: |*)

(*|

Components Helper Library
==========================
|*)

Fixpoint Valid_Subcomponents_Category
    (l : list component) (lcat : list ComponentCategory) :=
    match l with
        | nil => True
        | h :: t => In (h->category) lcat /\
            Valid_Subcomponents_Category t lcat
    end.

Lemma Valid_Subcomponents_Category_dec :
    forall (l:list component) (lcat :list ComponentCategory),
        { Valid_Subcomponents_Category l lcat } +
        { ~Valid_Subcomponents_Category l lcat }.
Proof.
    intros.
    unfold Valid_Subcomponents_Category.
    induction l.
    auto.
    apply dec_sumbool_and.
    - apply In_dec; apply ComponentCategory_eq_dec.
    - auto.
Qed.

Definition Well_Formed_Component_Subcomponents
    (c: component) (l : list ComponentCategory) :=
        Valid_Subcomponents_Category (c->subcomps) l.

Lemma Well_Formed_Component_Subcomponents_dec :
    forall (c:component) (lcat :list ComponentCategory),
        {Well_Formed_Component_Subcomponents c lcat} +
        { ~Well_Formed_Component_Subcomponents c lcat}.
Proof.
    intros.
    unfold Well_Formed_Component_Subcomponents.
    apply Valid_Subcomponents_Category_dec.
Qed.

(* Resolve component "name" in the subcomponents of c *)

Definition Resolve_Subcomponent_In_Component
    (name : identifier)
    (c : component)
    : option component
:=
    let results := filter (fun x => identifier_beq name (x->id)) (c->subcomps) in
    hd_error results.

(* Auxiliary function to resolve a subcomponnet in a hierarchy, starting from root. *)

Fixpoint Resolve_Subcomponent'
    (root : component)
    (path : list identifier)
    (name : identifier)
    (impl_name : option identifier)
    : option component
:=
    match path with
    | [] => Resolve_Subcomponent_In_Component name root
    | h :: t =>
        let node := Resolve_Subcomponent_In_Component h root in
            match node with
            | None => None
            | Some c => Resolve_Subcomponent' c t name impl_name
            end
    end.

Definition Resolve_Subcomponent
    (root : component)
    (fqn : fq_name)
    : option component
:=
    match fqn with
    | FQN path name impl => Resolve_Subcomponent' root path name impl
    end.

(*| * :coq:`Is_Same_Component_Type_classifier` returns True iff. :coq:`c1` and :coq:`c2` have the same component type classifier. |*)

Definition Is_Same_Component_Type_classifier (c1 c2: component) : Prop :=
    let (l1, i1, _) := c1->classifier in
    let (l2, i2, _) := c2->classifier in
        l1 = l2 /\ i1 = i2.

Lemma Is_Same_Component_Type_classifier_transitive: transitive _ Is_Same_Component_Type_classifier.
Proof.
    unfold transitive.
    intros c1 c2 c3.
    unfold Is_Same_Component_Type_classifier.

    intros.
    destruct (c1->classifier).
    destruct (c2->classifier).
    destruct (c3->classifier).
    intuition.
    rewrite H1 in * ; intuition.
    rewrite H2 in * ; intuition.
Qed.

(*| .. coq:: none |*)
End Helper_Functions.
(*| .. coq:: |*)
