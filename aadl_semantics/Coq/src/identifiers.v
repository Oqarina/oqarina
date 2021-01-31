(** ** identifiers.v *)

(** This file defines the identifier types *)

Require Export String.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Decidable.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import List.

(** ** Identifier type

The following is adapted from the chapter "Total and Partial Maps"
from Software Foundations, Vol. 1,

We use version 5.1 (july 2017),
from https://6826.csail.mit.edu/2017/lf/Maps.html#lab233

 *)

(** An identifier is a string element .. *)

Inductive identifier : Type :=
| Ident : string -> identifier.

Definition empty_identifier := Ident "".

(** Equality on identifier is a decidable proposition *)
Lemma ident_dec : forall id1 id2 : identifier, decidable(id1=id2).
Proof.
  unfold decidable.
  repeat decide equality.
Qed.

(** with an equality operation beq_ident .. *)

Definition beq_ident id1 id2 :=
  match id1,id2 with
  | Ident id1, Ident id2 => if string_dec id1 id2 then true else false
  end.

(** beq_ident is reflexive *)

Theorem beq_id_refl : forall id, true = beq_ident id id.
Proof.
  intros [n]. simpl. destruct (string_dec n n).
  - reflexivity.
  - destruct n0. reflexivity.
Qed.

(** beq_ident and equality on identifiers coincide *)

Theorem beq_id_true_iff : forall x y : identifier,
  beq_ident x y = true <-> x = y.
Proof.
   intros [n1] [n2].
   unfold beq_ident.
   destruct (string_dec n1 n2).
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct n. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : identifier,
  beq_ident x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

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

  rewrite <- beq_id_false_iff.
  rewrite <- beq_id_true_iff.
  destruct (ident_dec id empty_identifier).
  - subst. right. reflexivity.
  - subst. left. apply beq_id_false_iff. auto.
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
  destruct (ident_dec id empty_identifier).
  - subst. auto.
  - subst. auto.
Qed.

(** A boolean version of Well_Formed_Identifier *)

Definition Well_Formed_Identifier (i : identifier) : bool :=
  (negb (beq_ident i empty_identifier)).

(** Well_Formed_Identifier_Prop and Well_Formed_Identifier coincides *)

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

(** ** Examples *)

Example A_WFI : identifier :=
  Ident "o<".

Lemma A_WFI_is_well_formed_boring:
  Well_Formed_Identifier_prop A_WFI.
Proof.
  (* In this "boring" version, we do a manual proof using the
  previous definitions.

  First, we rewrite the proposition to its simple form *)
  unfold Well_Formed_Identifier_prop.
  unfold A_WFI.
  unfold empty_identifier.
  (* At this stage, we have to compare two Ident objects
     we apply the previously demonstrated theorem beq_if_false_iff
   *)
  apply beq_id_false_iff.
  (* Then we finish the proof *)
  simpl.
  reflexivity.
Qed.

Lemma A_WFI_is_well_formed:
  Well_Formed_Identifier_prop A_WFI.
Proof.
  (* In this variant, we take advantagd of the equivalence to the
  boolean predicate to proof this *)
  rewrite -> wf_coincide.
  auto.
Qed.

Lemma Empty_Identifier_is_ill_formed:
  Ill_Formed_Identifier_prop empty_identifier.
Proof.
  unfold Ill_Formed_Identifier_prop.
  reflexivity.
Qed.
