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
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.ListDec.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.legality.features_wf.
Require Import Oqarina.AADL.legality.properties_wf.
Require Import Oqarina.AADL.legality.connections_wf.
(*| .. coq:: |*)

(*|

Components
----------

In this section, we define several well-formedness rules for model elements.

For each rule, we define a basic predicate that operate on a component only,
without recursion. We demonstrate that this predicate is decidable.

|*)

(*| .. coq:: none |*)
Section WellFormedness_Rules.
(*| .. coq:: |*)

(*|

Generic rules

The AADL language defines some basic rules that are evaluated during the parsing of the model itself. We define them as a first validation step:
any component validates these rules.

|*)

(*| * Well-formedness of component identifiers: a component identifier is well-formed iff. the identifier is well-formed. |*)

Definition Well_Formed_Component_Id (c : component) : Prop :=
  (Well_Formed_Identifier_prop (c->id)).

(* * :coq:`Well_Formed_Component_Id` is a decidable property. *)

Lemma Well_Formed_Component_Id_dec : forall c : component,
  { Well_Formed_Component_Id c } + {~ Well_Formed_Component_Id c }.
Proof.
  prove_dec.
Qed.

Hint Resolve Well_Formed_Component_Id_dec : core.

(*| Well-formedness of component classifiers:  a component classifier is well-formed iff. the fq_name is well-formed. |*)

Definition Well_Formed_Component_Classifier (c : component) : Prop :=
  (Well_Formed_fq_name_prop (c->classifier)).

Lemma Well_Formed_Component_Classifier_dec : forall c : component,
  { Well_Formed_Component_Classifier c } + {~ Well_Formed_Component_Classifier c }.
Proof.
  generalize Well_Formed_fq_name_prop_dec.
  prove_dec.
Qed.

Hint Resolve Well_Formed_Component_Classifier_dec : core.

Definition Well_Formed_Component_Features (c : component) : Prop :=
  Well_Formed_Features (c->features).

Lemma Well_Formed_Component_Features_dec : forall c : component,
  { Well_Formed_Component_Features c } + {~ Well_Formed_Component_Features c }.
Proof.
  prove_dec.
Qed.

Hint Resolve Well_Formed_Component_Features_dec : core.

(*|
AADL legality rules
```````````````````
* Naming rule 4.3 (N2)

(N2)	Each component type has a local namespace for defining identifiers of prototypes, features, modes, mode transitions, and flow specifications. That is, defining prototype, defining feature, defining modes and mode transitions, and defining flow specification identifiers must be unique in the component type namespace.

|*)

(*| * Naming rule 4.5 (N1)

4.5 (N1) The defining identifier of a subcomponent declaration placed in a component implementation must be unique within the local namespace of the component implementation that contains the subcomponent.

_In other words, the list of identifiers built from the list of subcomponents has no duplicates_.

First, we define a predicate on list of subcomponents, and demonstrate it is decidable. |*)

Definition Subcomponents_Identifiers_Are_Unique (l : list component) : Prop :=
  NoDup (Components_Identifiers l).

Lemma Subcomponents_Identifiers_Are_Unique_dec :
  forall l : list component,
    dec_sumbool (Subcomponents_Identifiers_Are_Unique l).
Proof.
  prove_dec.
Qed.

(*| We can now "implement" the predicate for rule 4.5 (N1) |*)

Definition Rule_4_5_N1 (l : list component) : Prop :=
  Subcomponents_Identifiers_Are_Unique (l).

Lemma Rule_4_5_N1_dec :
  forall l : list component, { Rule_4_5_N1 l } + { ~ Rule_4_5_N1 l } .
Proof.
  generalize Subcomponents_Identifiers_Are_Unique_dec.
  prove_dec.
Qed.
Hint Resolve Rule_4_5_N1_dec : core.

Definition Well_Formed_Subcomponents (l : list component) :=
  Rule_4_5_N1 l.

Lemma Well_Formed_Subcomponents_cons: forall a l,
  Well_Formed_Subcomponents (a::l)
  -> Well_Formed_Subcomponents [a] /\ Well_Formed_Subcomponents l.
Proof.
  unfold Well_Formed_Subcomponents.
  unfold Rule_4_5_N1.
  unfold Subcomponents_Identifiers_Are_Unique.
  unfold Components_Identifiers.

  intros.
  simpl in H.
  apply NoDup_cons_iff in H.
  destruct H.
  intuition.
  prove_NoDup_singleton.
Qed.

Lemma Well_Formed_Subcomponents_in_resolve: forall l x,
  Well_Formed_Subcomponents l
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
      Get_Element_By_Name compare id. We first show that a and x have different id, then conclude. *)
      assert (a->id <> (x->id)).
      unfold Well_Formed_Subcomponents in H.
      unfold Rule_4_5_N1 in H.
      unfold Subcomponents_Identifiers_Are_Unique in H.
      unfold Components_Identifiers in H.
      simpl in H.
      apply NoDup_cons_iff in H.
      destruct H.
      assert (In (x->id)
                  (map (fun y => projectionComponentId y) l)).
      apply in_map. apply H0.
      eapply not_in_in.
      apply H.
      apply H2.

      (* We use the previous assertions to conclude. *)
      simpl.
      apply identifier_beq_neq in H1.
      simpl in H1.
      rewrite H1.

      apply Well_Formed_Subcomponents_cons in H.
      apply IHl ; intuition.
Qed.

(*| * Consistency rule 4.5 (C1)

The classifier of a subcomponent cannot recursively contain
subcomponents with the same component classifier. In other words, there cannot  be a cyclic containment dependency between components. |*)

  (* TBD *)

(*| * General validation rules

A component hierarchy verifies all the rules above.
These two master theorem combines them.

A component is well-formed iff. all the previous rules are validated:

* the component identifier is well-formed and
* its properties are correctly applied and
* subcomponents identifiers are well-formed  (Rule 4.5 N1)
|*)

Definition Well_Formed_Component (c : component) : Prop :=
  Well_Formed_Component_Id c /\
  Well_Formed_Component_Classifier c /\
  Well_Formed_Component_Features c /\
  Well_Formed_Connections c /\
  Well_Formed_Subcomponents (c->subcomps).

Lemma Well_Formed_Component_dec :
  forall c : component, dec_sumbool (Well_Formed_Component c).
Proof.
  prove_dec.
Defined.

(*| This theorem does not consider the component hierarchy, it is local to the component passed as parameter. THis is addressed by the following theorem.

A component hierarchy is well-formed iff a component and its subcomponent are well-formed. |*)

Definition Well_Formed_Component_Hierarchy (c : component) : Prop :=
  Unfold_Apply Well_Formed_Component c.

Lemma Well_Formed_Component_Hierarchy_dec:
  forall c : component, { Well_Formed_Component_Hierarchy c } + { ~Well_Formed_Component_Hierarchy c}.
Proof.
  prove_dec.
Defined.

(*|  This second theorem is the main theorem to assess a component is well-formed. It applies the previous rules on the whole component hierarchy. |*)

(*| .. coq:: none |*)
End WellFormedness_Rules.
(*| .. coq:: |*)

Global Hint Resolve Well_Formed_Component_Hierarchy_dec : core.
