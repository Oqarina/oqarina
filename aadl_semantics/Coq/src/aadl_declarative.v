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

(** AADL library *)
Require Import aadl.
Require Import aadl_wf.
Require Import identifiers.
Require Import utils.
(* end hide *)

(** * AADL component type and implementations

%In this chapter, we refine an AADL generic component into either a component type or a component implementation.\paragraph{}

\begin{definition}[AADL component type] An AADL component type is a well-formed generic AADL component without subcomponents and connections.
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
        forall c : component, { (Is_AADL_Component_Type (c)) } +
                              {~(Is_AADL_Component_Type (c))}.
    Proof.
        unfold Is_AADL_Component_Type.
        intros.
        repeat apply dec_sumbool_and; auto.
    Defined.

(* begin hide *)
End AADL_Component_Type.
(* end hide *)

(**
%\begin{definition}[AADL component implementation] An AADL component implementation is a well-formed generic AADL component.
\end{definition}%
*)

(* begin hide *)
Section AADL_Component_Implementation.
(* end hide *)

    Definition Is_AADL_Component_Implementation (c : component) : Prop :=
        Well_Formed_Component_Hierarchy c .

    Lemma Is_AADL_Component_Implementation_dec :
        forall c : component, { (Is_AADL_Component_Implementation (c)) } +
                              {~(Is_AADL_Component_Implementation (c))}.
    Proof.
        unfold Is_AADL_Component_Implementation.
        auto.
    Defined.

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

    (** %\begin{wfrule}An AADL package is well-formed iff its identifier is well-formed and its components are also well-formed. \end{wfrule}%*)

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