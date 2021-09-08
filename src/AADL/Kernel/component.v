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
(** %\chapter{Mechanizing the AADL component model}\label{chap::aadl_mecha}% *)

Set Warnings "-parsing".
(** printing -> %\ensuremath{\rightarrow}% *)
(** printing abstract %\coqdocvar{abstract}% *)

(* begin hide *)
(* XXX abstract is recognized as a tactic keyword by coqdoc .. this does not fully address the issue *)

(** Coq Library *)
Require Import Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Decimal.
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Sumbool.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.coq_utils.utils.
Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.AADL.Kernel.properties.
Open Scope list_scope.
(* end hide *)

(**

In this chapter, we define some core elements of the AADL component model in Coq. Our objective is to define the core concepts of AADL, helper functions to build models and to iterate over a hierarchy of AADL conponents.

This chapter assumes some familiarity of the AADL language version 2.2 %\cite{DBLP:books/daglib/0030032}% and of the Coq specification language. We used the book by A. Chlipala %\cite{DBLP:books/daglib/0035083}% as a reference to model AADL concepts using inductive dependent types.

*)

(** * AADL Component Model -- Concepts Definition

  In this section, we provide the core definition of AADL model elements. The names and hierarchy follows the textual grammar of the AADL Instance model. This Xtext grammar%\footnote{See \href{https://github.com/osate/osate2/blob/master/core/org.osate.aadl2.instance.textual/src/org/osate/aadl2/instance/textual/Instance.xtext}{Instance.xtext}}% provides a concise definition of the concepts that form an AADL model, an equivalent description can be found in AADL Instance meta-model. In chapter%~\ref{chap::aadl_decl}%, we show how to derive the concepts of component type, implementation and instances from these definitions.

  In the following, we provide a formalization of the AADL component model
  grammar as a collection of Coq inductive types.

  %\input{generated-content/categories}%

 *)

(* begin hide *)
Section AADL_Definitions.
(* end hide *)

 (** ** Definition of AADL Components

  An AADL component is made of an identifier, a category, a list of features, a list of properties, a list of subcomponents %\footnote{Flows and modes are subject to further discussions.}%. Per definition of the AADL component model, features and subcomponents list components as their parts. From a Coq perspective, we must define these three types as mutually dependent types at once.

  _Note: actually, this definition allows also for the definition of component type, implementation and instance. This is discussed in the next chapters_.

  *)

  Inductive component :=
  | Component : identifier ->          (* component identifier *)
                ComponentCategory ->   (* category *)
                fq_name ->             (* classifier, e.g. A::B::c.impl *)
                list feature ->        (* features *)
                list component ->      (* subcomponents *)
                list property_association -> (* properties *)
                list connection ->
                component
    with feature :=
      | Feature : identifier -> (* its unique identifier *)
                  DirectionType -> (* its direction *)
                  FeatureCategory -> (* category of the feature *)
                  component ->  (* corresponding component *)
                  list property_association -> (* properties *)
                  feature
    with connection :=
    | Connection : identifier ->
                   list identifier -> (* path to the source feature *)
                   list identifier -> (* path to the destination feature *)
                   connection.

  (** Definition of an empty component *)

  Definition nil_component :=
    Component empty_identifier (null) empty_fqname nil nil nil nil.

  (** Definition of an invalid feature *)

  Definition Invalid_Feature :=
    Feature (Id "invalid" ) inF invalid nil_component nil.

(* begin hide *)
End AADL_Definitions.
(* end hide *)

(** * Examples

  From the previous definitions, one can build a couple of examples showing how to build a set of AADL components. Note that one benefit of Coq is that we can build partial
  component elements as intermediate variables.

*)

(** - Definition of a component type and implementation *)

Definition A_Component := Component (Id "a_component") (abstract)
  (FQN [Id "pack1" ] (Id "foo_classifier") None) nil nil nil nil.

Definition A_Component_Impl :=
  Component (Id "a_component_impl")
  (abstract)
  (FQN [Id "pack1" ] (Id "foo_classifier") (Some (Id "impl")))  nil
  [ A_Component ] nil nil.

(** - Definition of a feature *)

Definition A_Feature := Feature (Id "a_feature") inF eventPort nil_component.

(** * Decidability of equality

Most of AADL model manipulations revolve around comparison of model subelements and iterations. In this section, we provide results on the decidability of equality.
*)

(** We use decision procedure (see https://softwarefoundations.cis.upenn.edu/vfa-current/Decide.html) so that we can perform code extraction. *)

(* begin hide *)
Section AADL_Component_Decidability.
(* end hide *)

(** For other types, we manually define and prove decidability for equality *)

  Lemma connection_eq_dec : eq_dec connection.
  Proof.
      unfold eq_dec.
      repeat decide equality.
  Qed.

  (* begin hide *)
  Hint Resolve connection_eq_dec DirectionType_eq_dec
      identifier_eq_dec ComponentCategory_eq_dec FeatureCategory_eq_dec
      property_association_eq_dec fq_name_eqdec

      : core.
  (* end hide *)

  (** Since component and features are mutually dependent, we first define a function that returns wether two components (resp. features) are equal. Then, we demonstrate the lemma for component.*)

  Fixpoint component_eq_dec' (a b : component) : {a=b}+{a<>b}
      with feature_eq_dec' (a b : feature) : {a=b}+{a<>b}.
  Proof.
      (* decide equality for component type *)
      decide equality;
      apply list_eq_dec; auto
      || auto.

      (* decide equality for feature type *)
      decide equality;
      apply list_eq_dec; auto
      || auto.
  Defined.

  Lemma component_eq_dec: eq_dec component.
  Proof.
      unfold eq_dec.
      intros.
      apply component_eq_dec'.
  Qed.

  Lemma feature_eq_dec: eq_dec feature.
  Proof.
      unfold eq_dec.
      intros.
      apply feature_eq_dec'.
  Defined.

  Lemma list_component_eq_dec : eq_dec (list component).
  Proof.
      unfold eq_dec.
      apply list_eq_dec.
      apply component_eq_dec.
  Qed.

  Lemma list_connection_eq_dec : eq_dec (list connection).
  Proof.
      unfold eq_dec.
      apply list_eq_dec.
      apply connection_eq_dec.
  Qed.

(* begin hide *)
End AADL_Component_Decidability.

Global Hint Resolve connection_eq_dec property_association_eq_dec DirectionType_eq_dec
  identifier_eq_dec ComponentCategory_eq_dec FeatureCategory_eq_dec component_eq_dec
  list_component_eq_dec list_connection_eq_dec : core.
(* end hide *)

(** * Accessor functions

  The following projections extract information from a component.
*)
(* begin hide *)
Section AADL_Accessors.
(* end hide *)

  (** ** Projections *)

  (** Projections are function returning parts of an inductive type. *)

  (** - Component *)

  Definition projectionComponentId (c : component) : identifier :=
    match c with
    | Component id _ _ _ _ _ _ => id
  end.

  Definition projectionComponentCategory (c:component) : ComponentCategory :=
    match c with
    | Component _ category _ _ _ _ _ => category
  end.

  Definition projectionComponentFeatures (c:component) : list feature :=
    match c with
    | Component _ _ _ features _ _ _ => features
  end.

  Definition projectionComponentSubComponents (c:component) : list component :=
    match c with
    | Component _ _ _ _ subComponents _ _ => subComponents
  end.

  Definition projectionComponentProperties (c:component) : list property_association :=
    match c with
    | Component _ _ _ _ _ properties _ => properties
  end.

  Definition projectionComponentConnections (c:component) : list connection :=
    match c with
    | Component _ _ _ _ _ _ connections => connections
  end.

  (** - Feature *)

  Definition projectionFeatureIdentifier (f : feature) : identifier :=
  match f with
  | Feature id _ _ _ _ => id
  end.

  Definition projectionFeatureDirection (f : feature) : DirectionType :=
    match f with
    | Feature _ d _ _ _ => d
  end.

  Definition projectionFeatureCategory (f : feature) : FeatureCategory :=
    match f with
    | Feature _ _ c _ _ => c
  end.

  Definition projectionFeatureComponent (f : feature) : component :=
    match f with
    | Feature _ _ _ comp _ => comp
    end.

  Definition projectionFeatureProperties (f : feature) : list property_association :=
    match f with
    | Feature _ _ _ _ lp => lp
    end.

  (** ** Helper functions *)

  (** These helper functions extract informations from component subclauses. *)

  (** [Features\_Components] return the list of components from the list of features [l].*)

  Definition Features_Components (l : list feature) : list component :=
    map (fun x => projectionFeatureComponent x) l.

  (** [Components\_Identifiers] return the list of identifiers in l. *)

  Definition Components_Identifiers (l : list component) : list identifier :=
    map (fun x => projectionComponentId x) l.

  (** %\coqdocdefinition{Unfold}% returns the list of components that are parts of c (e.g. as subcomponents) %\textbf{XXX features ??}%
  *)

  Fixpoint Unfold (c : component) : list component :=
    c ::
    ((fix Unfold_subcomponents (ls : list component) : list component :=
      match ls with
      | nil => nil
      | c :: lc  => Unfold (c) ++ Unfold_subcomponents (lc)
      end ) (projectionComponentSubComponents c)).

(* begin hide *)
End AADL_Accessors.
(* end hide *)

(** ** Notations

  These are helper notations to use the projections over AADL components: *)

Notation "c '->id' " := (projectionComponentId c)
  (at level 80, right associativity).
Notation "c '->category' " := (projectionComponentCategory c)
  (at level 80, right associativity).
Notation "c '->subcomps' " := (projectionComponentSubComponents c)
  (at level 80, right associativity).
Notation "c '->features' " := (projectionComponentFeatures c)
  (at level 80, right associativity).
Notation "c '->properties' " := (projectionComponentProperties c)
  (at level 80, right associativity).
Notation "c '->connections' " := (projectionComponentConnections c)
  (at level 80, right associativity).

(** * Iteration over AADL models

  Many properties or transformation rely on a traversal of the AADL model. In this section, we propose some reusable mechanisms for iterating over AADL models.

*)

(* begin hide *)
Section AADL_Iterators.
(* end hide *)

  (** ** Iteration over list of components *)

  (** In this section, we define a couple of mechanisms to evaluate
    a decidable predicate on a list of components. *)

  (** Let us suppose we have a predicate %\coqdocvar{P}% that is decidable. *)

  (* begin show *)
  Variable P : component -> Prop.
  Hypothesis HP : forall c : component, {P c} + {~P c}.
  (* end show *)

  (** Component_Iterate_List_prop applies predicate P on all elements of l, a list of component%\footnote{We are leveraging Coq section mechanism, therefore \coqdocvar{P} and \coqdocvar{HP} are part of the definition context, we do not need to make them visible in the definitions.}%. We then demonstrate that it yields a decidable proposition if P is decidable. *)

  Definition Component_Iterate_List_prop (l : list component) : Prop :=
    All P l.

  Lemma Component_Iterate_List_prop_dec :
    forall l : list component, {Component_Iterate_List_prop (l)} + {~Component_Iterate_List_prop (l)}.
  Proof.
    apply sumbool_All_dec.
    apply HP.
  Qed.

  (** Component_prop applies P on c, its features and its subcomponents.
   Let us note that this call does not recurse on the features and subcomponents.
    %\textbf{XXX should we keep it?}%
  *)

  Definition Component_prop (c : component) : Prop :=
    P c /\
    Component_Iterate_List_prop (Features_Components (c->features)) /\
    Component_Iterate_List_prop (c->subcomps).

  Lemma Component_prop_dec :
    forall c : component, { Component_prop c } + {~ Component_prop c }.
  Proof.
    intros.
    unfold Component_prop.
    apply dec_sumbool_and.
    - apply HP.
    - apply dec_sumbool_and; apply Component_Iterate_List_prop_dec.
  Qed.

  (** ** Iteration over a component hierarchy  *)

  (**

  Actually, we may want a more generic iterator that would iterate on the whole hierarchy. A component is nothing but a representation of a tree of AADL components. We could imagine implementing a traversal algorithm based on a visitor pattern like the following.

  However, Coq has a strict definition of recursive functions, and the following is rejected

[[
  Fixpoint Component_prop (lc : list component) : Prop :=
      match lc with
      | [ ] => True
      | c :: l' => P c /\
      Component_prop (Features_Components (c->features)) /\
      Component_prop (l')
      end. ]]

  Such a definition is rejected as it is not strictly decreasing on the main argument [lc] because of the recursive call [Features_Components (c->features)].
*)

(** **** Iterating via unfolding:

  one possible work-around is to apply P on the list of components built recursively from component c using %\coqdocdefinition{Unfold}%. The decidability of the resulting function is a direct result of the decidablity of %\coqdocdefinition{All P}% for %\coqdocdefinition{P}% decidable. *)

Definition Unfold_Apply (c : component) : Prop :=
  All P (Unfold c).

 Theorem Unfold_Apply_dec : forall c : component,
  { Unfold_Apply c } + { ~Unfold_Apply c }.
 Proof.
   intros.
   unfold Unfold_Apply.
   apply sumbool_All_dec.
   apply HP.
 Qed.

 (* begin hide *)
 (** **** Iterating via recursion over the component hierarchy. *)

(* TBD, prototype is easy to build, the issue is on proving its decidability.
  Crafting and using the correct induction principle seems problematic. *)

 (* end hide *)

(* begin hide *)
End AADL_Iterators.
(* end hide *)
