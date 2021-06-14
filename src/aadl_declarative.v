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
Require Import Oqarina.aadl_categories.
Require Import Oqarina.aadl.
Require Import Oqarina.aadl_wf.
Require Import Oqarina.core.identifiers.
Require Import Oqarina.coq_utils.utils.
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
%\wfrule{AADL component type well-formedness}{}{An AADL component type is well-formed iff. its features match some restrictions imposed by its category.}%
*)

(** XXX Actually wrong, we must check for the direction of the feature as well *)

    Fixpoint Valid_Features_Category
        (l : list feature) (lcat : list FeatureCategory) :=
            match l with
            | nil => True
            | h :: t => In (projectionFeatureCategory  h) lcat /\
                        Valid_Features_Category t lcat
            end.

    Lemma Valid_Features_Category_dec :
        forall (l:list feature) (lcat :list FeatureCategory),
            { Valid_Features_Category l lcat } +
            { ~Valid_Features_Category l lcat }.
    Proof.
        intros.
        unfold Valid_Features_Category.
        induction l.
        auto.
        apply dec_sumbool_and.
        - apply In_dec; apply FeatureCategory_eq_dec.
        - auto.
    Qed.

    Definition Well_Formed_Component_Type
        (c: component) (l : list FeatureCategory) :=
            Is_AADL_Component_Type c /\
            Valid_Features_Category (c->features) l.

    Lemma Well_Formed_Component_Type_dec :
        forall (c:component) (lcat :list FeatureCategory),
            {Well_Formed_Component_Type c lcat} +
            { ~Well_Formed_Component_Type c lcat}.
    Proof.
        intros.
        unfold Well_Formed_Component_Type.
        apply dec_sumbool_and.
        apply Is_AADL_Component_Type_dec.
        apply Valid_Features_Category_dec.
      Qed.

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

    Definition Well_Formed_Component_Implementation
        (c: component) (l : list ComponentCategory) :=
            Is_AADL_Component_Implementation c /\
            Valid_Subcomponents_Category (c->subcomps) l.

    Lemma Well_Formed_Component_Implementation_dec :
        forall (c:component) (lcat :list ComponentCategory),
            {Well_Formed_Component_Implementation c lcat} +
            { ~Well_Formed_Component_Implementation c lcat}.
    Proof.
        intros.
        unfold Well_Formed_Component_Implementation.
        apply dec_sumbool_and.
        apply Is_AADL_Component_Implementation_dec.
        apply Valid_Subcomponents_Category_dec.
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