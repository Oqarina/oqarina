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
(** %\chapter{Well-formedness rules of an AADL model}\label{chap::aadl_wf}% *)

(* begin hide *)

(** Coq Library *)
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.ListDec.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.component.
Require Import Oqarina.core.identifiers.
Require Import Oqarina.coq_utils.utils.
Require Import Oqarina.AADL.Kernel.properties.
(* end hide *)

(**

In this section, we define several well-formedness rules for model elements.

For each rule, we define a basic predicate that operate on a component only,
without recursion. We demonstrate that this predicate is decidable.

*)
(* begin hide *)
Section WellFormedness_Rules.
(* end hide *)

  (** * Generic rules

  The AADL language defines some basic rules that are evaluated during the
  parsing of the model itself. We define them as a first validation step:
   any component validates these rules.

  *)

  (** ** Well-formedness of component identifiers *)

  (** A component identifier is well-formed iff. the identifier is well-formed. *)

  Definition Well_Formed_Component_Id (c : component) : Prop :=
    (Well_Formed_Identifier_prop (c->id)).

  (** Well_Formed_Component_Id is a decidable property. *)

  Lemma Well_Formed_Component_Id_dec : forall c : component,
    { Well_Formed_Component_Id c } + {~ Well_Formed_Component_Id c }.
  Proof.
    (* Hint: this is a direct consequence of the decidability of the
       well-formedness rule of identifiers *)
    intros.

    (* unfold the various definitions *)
    unfold dec_sumbool.
    unfold Well_Formed_Component_Id.

    (* apply decidability result on Identifier *)
    apply Well_Formed_Identifier_prop_dec.
  Qed.

  (* begin hide *)
  Hint Resolve Well_Formed_Component_Id_dec : core.
  (* end hide *)

  (** ** Well-formedness of component classifiers *)

  (** A component classifier is well-formed iff. the fq_name is well-formed. *)

  Definition Well_Formed_Component_Classifier (c : component) : Prop :=
    (Well_Formed_fq_name_prop (c->classifier)).

  (** Well_Formed_Component_Id is a decidable property. *)

  Lemma Well_Formed_Component_Classifier_dec : forall c : component,
    { Well_Formed_Component_Classifier c } + {~ Well_Formed_Component_Classifier c }.
  Proof.
    intros.

    unfold Well_Formed_Component_Classifier.
    apply Well_Formed_fq_name_prop_dec.
  Qed.

  (* begin hide *)
  Hint Resolve Well_Formed_Component_Classifier_dec : core.
  (* end hide *)

  (** * AADL legality rules *)

  (** ** Naming rule 4.5 (N1) *)
  (** 4.5 (N1) The defining identifier of a subcomponent declaration placed in a
  component implementation must be unique within the local namespace of the
  component implementation that contains the subcomponent.

  _Hint: In other words, the list of identifiers built from the list of subcomponents has no duplicates_.

  First, we define a predicate on list of subcomponents, and demonstrate it is decidable.

  *)

  Definition Subcomponents_Identifiers_Are_Well_Formed (l : list component) : Prop :=
    (NoDup (Components_Identifiers l)).

  Lemma Subcomponents_Identifiers_Are_Well_Formed_dec :
    forall l : list component,
      dec_sumbool (Subcomponents_Identifiers_Are_Well_Formed l).
  Proof.
    intros.

    (* unfold the various definitions *)
    unfold dec_sumbool.
    unfold Subcomponents_Identifiers_Are_Well_Formed.

    apply NoDup_dec. (* NoDup is decidable, from Coq.Lists.ListDec *)

    (* Last bit is to rely on identifier equality being also decidable *)
    unfold decidable_eq. (* from Coq.Lists.ListDec *)
    apply identifier_eq_dec. (* from utils *)
  Qed.

  (** We can now "implement" the predicate for rule 4.5 (N1) *)

  Definition Rule_4_5_N1 (c : component) : Prop :=
    Subcomponents_Identifiers_Are_Well_Formed (c->subcomps).

  Lemma Rule_4_5_N1_dec :
    forall c : component, { Rule_4_5_N1 c } + { ~ Rule_4_5_N1 c } .
  Proof.
    unfold Rule_4_5_N1.
    intros.
    apply Subcomponents_Identifiers_Are_Well_Formed_dec.
  Qed.

  (* begin hide *)
  Hint Resolve Rule_4_5_N1_dec : core.
  (* end hide *)

  (** ** Consistency rule 4.5 (C1) *)
  (** 4.5 (C1)	The classifier of a subcomponent cannot recursively contain
    subcomponents with the same component classifier. In other words, there cannot
    be a cyclic containment dependency between components.

  *)

  (* TBD *)

  (** * General validation rules *)

  (** A component hierarchy verifies all the rules above.
      These two master theorem combines them.

  %\paragraph{}\wfrule{[Master theorem \#1}{well-formed!component}{
  A component is well-formed iff. all the previous rules are validated:
  \begin{itemize}
    \item the component identifier is well-formed and
    \item its properties are correctly applied and
    \item subcomponents identifiers are well-formed  (Rule 4.5 N1) and
  \end{itemize}
  }%
 *)

  Definition Well_Formed_Component (c : component) : Prop :=
   Well_Formed_Component_Id (c) /\
   Well_Formed_Component_Classifier (c) /\
  (* Well_Formed_Properties (c) /\ *)
   Rule_4_5_N1 (c).

  Lemma Well_Formed_Component_dec :
    forall c : component, dec_sumbool (Well_Formed_Component c).
  Proof.
    (* Unfold all definitions *)
    intros.
    unfold Well_Formed_Component.

    (* Apply decidability results *)
    apply dec_sumbool_and; auto.
    apply dec_sumbool_and; auto.

    (* Note: auto requires all theorems to be part of the core hints
    database, see above "Hint Resolve Rule_4_5_N1_dec : core."  *)
  Defined.

  (** This theorem does not consider the component hierarchy, it is local to
  the component passed as parameter. THis is addressed by the following theorem.

  %\paragraph{}\wfrule{Master theorem \# 2}{well-formed!component hierarchy}{
  A component hierarchy is well-formed iff a component and its subcomponent are well-formed.
  }%
  *)

  Definition Well_Formed_Component_Hierarchy (c : component ) : Prop :=
    Unfold_Apply Well_Formed_Component c.

  Lemma Well_Formed_Component_Hierarchy_dec:
    forall c : component, { Well_Formed_Component_Hierarchy c } + { ~Well_Formed_Component_Hierarchy c}.
  Proof.
    intros.
    unfold Well_Formed_Component_Hierarchy.
    apply Unfold_Apply_dec.
    apply Well_Formed_Component_dec.
  Defined.

(**  This second theorem is the main theorem to assess a component is well-formed. It applies the previous rules on the whole component hierarchy. *)

(* begin hide *)
End WellFormedness_Rules.

Global Hint Resolve Well_Formed_Component_Hierarchy_dec : core.

(* end hide *)
