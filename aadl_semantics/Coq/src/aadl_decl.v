(** %\chapter{AADL declarative model}\label{chap::aadl_decl}% *)

(**
In the previous chapter, we introduced a generic component model that matches the concepts of AADL component type, implementation and instances. In this chapter. we show how to specialize this model to support the AADL declarative model.

_Note: the following concepts of AADL are excluded: arrays, modes, flows_.

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

The definition we proposed for an AADL generic component in the previous chapter covers both component type and implementation. In this chapter, we propose some definitions to refine an AADL generic component into either a component type or a component implementation. *)

(**
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
%\begin{definition}[AADL component implenentation] An AADL component implementation is a well-formed generic AADL component.
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

(**
%\begin{definition}[AADL package] An AADL package is a named-list of AADL components.
\end{definition}%
*)

(* begin hide *)
Section AADL_Package.
(* end hide *)

    Inductive package :=
        | Package : identifier -> list component -> package.




(* begin hide *)
End AADL_Package.
(* end hide *)