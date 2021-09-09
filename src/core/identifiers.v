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
(** %\chapter{identifiers.v -- Identifier type} %*)

(** This file defines the identifier type, a basic type that stores a string. *)

(* begin hide *)
(** Coq Library *)
Require Export String.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Decidable.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import List.

(** Oquarina *)
Require Import Oqarina.coq_utils.utils.
(* end hide *)

(** * Identifier type *)

(**
%\define{Identifier}{identifier}{An identifier is a string element. It is supported by an equality scheme, and a notation to extract the string from the type.}
*)

Inductive identifier : Type :=
| Id (name : string).

Definition empty_identifier := Id "".

Scheme Equality for identifier.

Definition projectionIdentifierString (i : identifier) : string :=
  match i with
  | Id s => s
  end.

Notation "c '->toString' " := (projectionIdentifierString c)
                                (at level 80, right associativity).

Lemma identifier_beq_eq: forall id1 id2,
    identifier_beq id1 id2 = true <-> id1 = id2.
Proof.
  split.
  - apply internal_identifier_dec_bl.
  - apply internal_identifier_dec_lb.
Qed.

Lemma id_beqP :  forall id1 id2,
    reflect (id1 = id2) (identifier_beq id1 id2).
Proof.
  intros. apply iff_reflect. symmetry. apply identifier_beq_eq.
Qed.

(** [fq_name] defines a fully qualified nane for component classifiers, e.g. "A::B::C (.impl)" *)

Inductive fq_name :=
| FQN (path : list identifier) (name : identifier) (impl_name : option identifier).

Lemma fq_name_eqdec  : eq_dec fq_name.
Proof.
    unfold eq_dec.
    repeat decide equality.
Defined.

Definition empty_fqname : fq_name := FQN nil empty_identifier None.

(** [ps_qname] defines a qualified name for property related construct, e.g.  "foo::bar" *)

Inductive ps_qname :=
| PSQN (psname : string) (name : string).

Scheme Equality for ps_qname.

(**
%\wfrule{Well-formed identifier}{well-formed!identifier}{An identifier is well-formed iff it is not the empty identifier.
\textit{Rationale: an identifier being used to identify a model element, it
must be trivially non empty.}
}%

XXX Actually, we could check for more things like this is ASCII, no whitespace, etc. See https://github.com/clarus/coq-list-string for an API to make this easy.

*)

Definition Well_Formed_Identifier_prop (i : identifier) : Prop :=
  (i <> empty_identifier).

Lemma Well_Formed_Identifier_prop_dec: forall id: identifier,
  { Well_Formed_Identifier_prop id } + { ~ Well_Formed_Identifier_prop id }.
Proof.
  intros.
  unfold Well_Formed_Identifier_prop.
  destruct (identifier_eq_dec id empty_identifier).
  - subst. auto.
  - subst. auto.
Qed.

(** * Examples *)

Example A_WFI : identifier :=
  Id "o<".

Lemma A_WFI_is_well_formed:
  Well_Formed_Identifier_prop A_WFI.
Proof.
  (* In this "boring" version, we do a manual proof using the
  previous definitions.

  First, we rewrite the proposition to its simple form *)
  unfold Well_Formed_Identifier_prop.
  destruct (identifier_eq_dec A_WFI empty_identifier).
  inversion e. auto.
Qed.

Lemma Empty_Identifier_is_ill_formed:
  ~ Well_Formed_Identifier_prop empty_identifier.
Proof.
  unfold Well_Formed_Identifier_prop.
  auto.
Qed.
