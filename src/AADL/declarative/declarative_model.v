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
(** %\chapter{AADL declarative model}\label{chap::aadl_decl}% *)

(**
In the previous chapter, we introduced a generic component model that matches the concepts of AADL component type, implementation and instances. In this chapter. we show how to specialize this model to support the AADL declarative model%\footnote{Note: the following concepts of AADL are excluded: arrays, modes, flows}%.

*)

(* begin hide *)
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
(* end hide *)

(**

In this chapter, we refine an AADL generic component into either a component type or a component implementation. We then introduce the concept of AADL packages as a collection of components, and AADL model has a collection of packages.

* AADL Component Type

%\begin{definition}[AADL component type] An AADL component type is a well-formed generic AADL component without subcomponents and connections.
\end{definition}%
*)

(* begin hide *)
Section AADL_Component_Type.
(* end hide *)

    Definition Is_AADL_Component_Type (c : component) : Prop :=
        Well_Formed_Component_Hierarchy c /\
        c->subcomps = nil /\
        c->connections = nil.

    Lemma Is_AADL_Component_Type_dec :
        forall c : component, { Is_AADL_Component_Type c } +
                              { ~Is_AADL_Component_Type c }.
    Proof.
        unfold Is_AADL_Component_Type.
        intros.
        repeat apply dec_sumbool_and; auto.
    Defined.

(**
%\wfrule{AADL component type well-formedness}{}{An AADL component type is well-formed iff. its features match some restrictions imposed by its category, and it is itself a well-formed component.}%
*)

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
        intros.
        unfold Well_Formed_Component_Type.
        apply dec_sumbool_and.
        apply Is_AADL_Component_Type_dec.
        apply dec_sumbool_and.
        apply Well_Formed_Component_Type_Interface_dec.
        apply dec_sumbool_and.
        apply Well_Formed_Component_dec.
        apply Well_Formed_Property_Associations_dec.
    Defined.

(* begin hide *)
End AADL_Component_Type.
(* end hide *)

(** * AADL Component Implementation

%\begin{definition}[AADL component implementation] An AADL component implementation is a well-formed generic AADL component.
\end{definition}% *)

(* begin hide *)
Section AADL_Component_Implementation.
(* end hide *)

    Definition Is_AADL_Component_Implementation (c : component) : Prop :=
        Well_Formed_Component_Hierarchy c .

    Lemma Is_AADL_Component_Implementation_dec :
        forall c : component, { Is_AADL_Component_Implementation c } +
                              { ~Is_AADL_Component_Implementation c}.
    Proof.
        unfold Is_AADL_Component_Implementation.
        auto.
    Defined.

(**
%\wfrule{AADL component implementation well-formedness}{}
{An AADL component implementation is well-formed iff. its subcomponents match some restrictions imposed by its category.}%
*)

    Definition Well_Formed_Component_Implementation' (c: component) :=
        Is_AADL_Component_Implementation c /\
        Well_Formed_Component_Implementation_Subcomponents c /\
        Well_Formed_Component c /\
        Well_Formed_Property_Associations c AADL_Predeclared_Property_Sets.

    Lemma Well_Formed_Component_Implementation'_dec :
    forall (c:component),
        {Well_Formed_Component_Implementation' c} +
        { ~Well_Formed_Component_Implementation' c}.
    Proof.
        intros.
        unfold Well_Formed_Component_Implementation'.
        apply dec_sumbool_and.
        apply Is_AADL_Component_Implementation_dec.
        apply dec_sumbool_and.
        apply Well_Formed_Component_Implementation_Subcomponents_dec.
        apply dec_sumbool_and.
        apply Well_Formed_Component_dec.
        apply Well_Formed_Property_Associations_dec.
    Defined.

    Definition Well_Formed_Component_Implementation (c: component) :=
        Unfold_Apply Well_Formed_Component_Implementation' c.

    Lemma Well_Formed_Component_Implementation_dec :
        forall (c:component),
            {Well_Formed_Component_Implementation c} +
            { ~Well_Formed_Component_Implementation c}.
    Proof.
        unfold Well_Formed_Component_Implementation.
        apply Unfold_Apply_dec.
        apply Well_Formed_Component_Implementation'_dec.
    Qed.

(* begin hide *)
End AADL_Component_Implementation.
(* end hide *)

(** * AADL package

%\begin{definition}[AADL package] An AADL package is a named-list of AADL components.
\end{definition}%
*)

(* begin hide *)
Section AADL_Package.
(* end hide *)

    Inductive package :=
        | Package : identifier -> list component -> package.

(** From this definition; we also define a decidable equality principle, projection functions, etc. *)

    Lemma package_eq_dec : eq_dec package.
    Proof.
        unfold eq_dec.
        repeat decide equality.
    Qed.

    Definition projectionPackageId (p : package) : identifier :=
        match p with
        | Package id _ => id
        end.

    Definition projectionPackageComponents (p : package) : list component :=
        match p with
        | Package  _ lp => lp
        end.

    Notation "p '->idp' " := (projectionPackageId p)
        (at level 80, right associativity).

    Notation "p '->components' " := (projectionPackageComponents p)
        (at level 80, right associativity).

    (** %\wfrule{Well-formed AADL package}{}{An AADL package is well-formed iff its identifier is well-formed and its components are also well-formed.}%*)

    Definition Well_Formed_Package (p : package) :=
        Well_Formed_Identifier_prop (p->idp) /\
        All Well_Formed_Component (p->components).

    Lemma Well_Formed_Package_dec :
        forall p : package, { Well_Formed_Package p } + { ~Well_Formed_Package p }.
    Proof.
        intros.
        unfold Well_Formed_Package.
        apply dec_sumbool_and.
        apply Well_Formed_Identifier_prop_dec.
        apply sumbool_All_dec.
        apply Well_Formed_Component_dec.
    Qed.

(** At this stage, we simply have collection of well-formed packages. But this is not enough to guarantee the model is correct. We need to add some typing rules that assess all elements are properly resolved. This is addressed in the next sections. *)

(* begin hide *)
End AADL_Package.
(* end hide *)

(** * AADL model as transitive closure

%So far, we have defined fragments of AADL: component types, implementations and packages. We now define an AADL model as a collection of AADL packages.

\begin{definition}[AADL model] An AADL model is a list of AADL packages.\end{definition}%
*)

(* begin hide *)
Section AADL_Model.
(* end hide *)

    Definition AADL_Model := list package.

(** XXX from this definition, we can build all legality rules we want *)

(* begin hide *)
End AADL_Model.
(* end hide *)