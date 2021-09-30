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
Require Import Oqarina.AADL.legality.all.
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.utils.
Require Import Oqarina.AADL.declarative.all.
Require Import Oqarina.cpdttactics.
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

    Definition Well_Formed_Component_Instance (c : component) :=
        Well_Formed_Component_Implementation c.

    Lemma Well_Formed_Component_Instance_dec :
        forall (c:component),
            {Well_Formed_Component_Instance c } +
            { ~Well_Formed_Component_Instance c }.
    Proof.
        intros.
        unfold Well_Formed_Component_Instance.
        apply Well_Formed_Component_Implementation_dec.
    Defined.

(* begin hide *)
End AADL_Instance.
(* end hide *)

(** The [prove_Is_AADL_Instance] helps proving a component is a valid AADL instance *)

Ltac prove_Is_AADL_Instance :=
    repeat match goal with
      | |- Is_AADL_Instance _ => compute; repeat split; auto
      | |- (_ =  EmptyString -> False) => intuition; inversion H
      | |- NoDup nil => apply NoDup_nil
      | |- NoDup  _  => apply NoDup_cons ; crush
      | |- ~ In _ _ => intuition
    end.

Ltac prove_Well_Formed_Component_Instance :=
    repeat match goal with
      | |- Well_Formed_Component_Instance _ => compute; repeat split; auto
      | |- (_ =  EmptyString -> False) => intuition; inversion H
      | |- NoDup nil => apply NoDup_nil
      | |- NoDup  _  => apply NoDup_cons ; crush
      | |- ~ In _ _ => intuition
    end.