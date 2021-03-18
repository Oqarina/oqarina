(** %\chapter{identifiers.v -- Identifier type} %*)

(** This file defines the identifier type, a basic type that stores a string. *)

Require Export String.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Decidable.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import List.

Require Import utils.
(** * Identifier type *)

(** An identifier is a string element *)

Inductive identifier : Type :=
| Ident : string -> identifier.

Definition empty_identifier := Ident "".

(** Equality on identifier is a decidable proposition *)
Scheme Equality for identifier.

Lemma ident_dec : forall id1 id2 : identifier, decidable(id1=id2).
Proof.
  unfold decidable.
  repeat decide equality.
  Qed.


(** .. an accessor method *)

Definition projectionIdentifierString (i : identifier) : string :=
  match i with
  | Ident s => s
  end.

Notation "c '->toString' " := (projectionIdentifierString c)
                                (at level 80, right associativity).

(** .. and a definition of a well-formed identifier

An identifier is well-formed iff it is not the empty identifier.

Rationale: an identifier being used to identify a model element, it
must be trivially non empty.

XXX Actually, we could check for more things like this is ASCII, no whitespace, etc.
See https://github.com/clarus/coq-list-string for an API to make this easy.

*)
Definition Well_Formed_Identifier_prop (i : identifier) : Prop :=
  (i <> empty_identifier).

Definition Ill_Formed_Identifier_prop (i : identifier) : Prop :=
  (i = empty_identifier).

Lemma wf_is_not_if: forall id: identifier,
  Well_Formed_Identifier_prop id <-> ~ Ill_Formed_Identifier_prop id.
Proof.
  (* We simply unfold definitions. Note that Coq interpreter will
     automatically adjust the equalities to suppress the ~ (not) operator.
  *)
  unfold Ill_Formed_Identifier_prop.
  unfold Well_Formed_Identifier_prop.
  reflexivity.
Qed.

Lemma if_is_not_wf: forall id: identifier,
  Ill_Formed_Identifier_prop id <-> ~ Well_Formed_Identifier_prop id.
Proof.
  intros.

  (* Use previously demonstrated result *)
  rewrite -> wf_is_not_if.
  split.

  (* prove Ill_Formed_Identifier_prop id -> ~ ~ Ill_Formed_Identifier_prop id *)
  intros.
  auto.

  (* prove ~~ Ill_Formed_Identifier_prop id -> Ill_Formed_Identifier_prop id *)
  apply NNPP.  (* uses Coq.Logic.Classical_Prop *)
Qed.

(** An identifier is either well-formed or ill-formed *)

  Lemma wf_dec : forall id: identifier,
  Well_Formed_Identifier_prop id \/ Ill_Formed_Identifier_prop id.
Proof.
  intros.
  unfold Well_Formed_Identifier_prop.
  unfold Ill_Formed_Identifier_prop.
  destruct (identifier_eq_dec id empty_identifier).
  - right. apply e.
  - left. apply n.
Qed.

(** Well_Formed_Identifier_prop is decidable *)

Theorem Well_Formed_Identifier_prop_dec: forall id: identifier,
  decidable (Well_Formed_Identifier_prop id).
Proof.
  intros.

  (* apply definitions *)
  unfold decidable.
  unfold Well_Formed_Identifier_prop.

  (* do a case by case analysis *)
  destruct (identifier_eq_dec id empty_identifier).
  - subst. auto.
  - subst. auto.
Qed.

(** A boolean version of Well_Formed_Identifier *)
(*
Definition Well_Formed_Identifier (i : identifier) : bool :=
  (negb (beq_ident i empty_identifier)).
*)
(** Well_Formed_Identifier_Prop and Well_Formed_Identifier coincides *)
(*
Lemma wf_coincide: forall id: identifier,
  Well_Formed_Identifier_prop id <-> Well_Formed_Identifier id = true.
Proof.
  intros.
  unfold Well_Formed_Identifier_prop.
  unfold Well_Formed_Identifier.
  rewrite <- beq_id_false_iff.
  unfold negb.
  split.
  - intuition. rewrite H. reflexivity.
  - destruct (beq_ident id empty_identifier) . auto. auto.
Qed.
*)
(** * Examples *)

Example A_WFI : identifier :=
  Ident "o<".

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
  Ill_Formed_Identifier_prop empty_identifier.
Proof.
  unfold Ill_Formed_Identifier_prop.
  reflexivity.
Qed.
