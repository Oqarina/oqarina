(** %\chapter{AADL instance model}\label{chap::aadl_instance}% *)

(**
In the previous chapter, we introduced a generic component model that matches the concepts of AADL component type, implementation and instances. In this chapter. we show how to specialize this model to support the AADL instance model.

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
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.utils.
(* end hide *)

(** * AADL instance model

%In this chapter, we refine an AADL generic component into  an AADL instance model.\paragraph{}

\begin{definition}[AADL instance model] An AADL instance model is a well-formed generic AADL component.
\end{definition}%
*)

(* begin hide *)
Section AADL_Instance.
(* end hide *)

    Definition Is_AADL_Instance (c : component) : Prop :=
        Well_Formed_Component_Hierarchy c.

    Lemma Is_AADL_Instance_dec :
        forall c : component, { Is_AADL_Instance c } +
                              { ~Is_AADL_Instance c }.
    Proof.
        unfold Is_AADL_Instance.
        intros.
        repeat apply dec_sumbool_and; auto.
    Defined.

(* begin hide *)
End AADL_Instance.
(* end hide *)