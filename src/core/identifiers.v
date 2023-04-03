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
Require Import BinNat Ascii.

(** Oquarina *)
Require Import Oqarina.coq_utils.all.
(* end hide *)

Section ASCII_Helpers.

  (* The following adds basic string manipulation functions. We might consider moving them in a separate file. *)

  Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

  Definition is_alpha c :=
    ((("a" <=? c) && (c <=? "z")) ||
    (("A" <=? c) && (c <=? "Z")) ||
    (c =? "_"))%char.

  Definition starts_with_letter s1  :=
    match s1 with
      | EmptyString => false
      | String head tail => (is_alpha head)
    end.

  Fixpoint has_only_alphanum s :=
    match s with
    | EmptyString => true
    | String head tail => ((is_alpha head) || (is_digit head)) && (has_only_alphanum tail)
    end.

End ASCII_Helpers.

(** * Identifier type *)

(**
%\define{Identifier}{identifier}{An identifier is a string element. It is supported by an equality scheme, and a notation to extract the string from the type.}
*)

Inductive identifier : Type :=
| Id (name : string).

Definition empty_identifier := Id "".

Scheme Equality for identifier.

Lemma identifier_string_eq (s1 s2 : string) : s1 = s2 <-> Id s1 = Id s2.
Proof.
  split.
  - apply f_equal.
  - intros H1. injection H1. auto.
Qed.

Lemma identifier_string_neq (s1 s2 : string) : s1 <> s2 <-> Id s1 <> Id s2.
Proof.
  rewrite <- identifier_string_eq. easy.
Qed.

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

Lemma identifier_beq_neq: forall id1 id2,
    identifier_beq id1 id2 = false <-> id1 <> id2.
Proof.
  intros.
  rewrite <- identifier_beq_eq.
  rewrite not_true_iff_false. reflexivity.
Qed.

Lemma id_beqP :  forall id1 id2,
    reflect (id1 = id2) (identifier_beq id1 id2).
Proof.
  intros. apply iff_reflect. symmetry. apply identifier_beq_eq.
Qed.

(** [id_in] return true if [id] is in list [l] *)

Definition id_in (id : identifier) (l : list identifier) :=
  existsb (fun x => (identifier_beq id x)) l.

(** [fq_name] defines a fully qualified nane for component classifiers, e.g. "A::B::C (.impl)" *)

Inductive fq_name :=
| FQN (path : list identifier) (name : identifier) (impl_name : option identifier).

Lemma fq_name_eq_dec : forall x y : fq_name, {x = y} + {x <> y}.
Proof.
    repeat decide equality.
Defined.

Definition empty_fqname : fq_name := FQN nil empty_identifier None.

(** [feature_ref] defines a feature reference, e.g. "comp.feature" *)

Inductive feature_ref := | FREF (compname : string) (featurename : string).

Definition empty_feature_ref := FREF "" "".

Scheme Equality for feature_ref.

(** [ps_qname] defines a qualified name for property related construct, e.g.  "foo::bar" *)

Inductive ps_qname :=
| PSQN (psname : string) (name : string).

Definition empty_ps_qname := PSQN "" "".

Scheme Equality for ps_qname.

(**
%\wfrule{Well-formed identifier}{well-formed!identifier}{An identifier is well-formed iff it is not the empty identifier.
\textit{Rationale: an identifier being used to identify a model element, it
must be trivially non empty.}
}%

*)
  (** [Is_true] defines a mapping from [bool] to [Prop], this mechanism is relevant to build decidable properties out of basic boolean predicates. The [Is_true_dec] tactic expediates the proof of decidability functions based on [Is_true]. *)

Ltac Is_true_dec :=
  repeat match goal with
    | |- forall _, { ?T _ } + { ~ ?T _} => intros; unfold T
    | |- {Is_true (_)} + {~ Is_true (_)}  => destruct (_); simpl; auto
   end.

  Definition Well_Formed_string_prop (s : string) : Prop :=
    (s <> EmptyString) /\
    Is_true (starts_with_letter s &&
             has_only_alphanum s).

  Lemma Well_Formed_string_prop_dec: forall s : string,
    { Well_Formed_string_prop s } + { ~ Well_Formed_string_prop s }.
  Proof.
    intros.
    unfold Well_Formed_string_prop.
    apply dec_sumbool_and.
    destruct (string_dec s EmptyString); subst; auto.
    Is_true_dec.
  Qed.

Definition Well_Formed_Identifier_prop (i : identifier) : Prop :=
  Well_Formed_string_prop (i ->toString).

Lemma Well_Formed_Identifier_prop_dec: forall id: identifier,
  { Well_Formed_Identifier_prop id } + { ~ Well_Formed_Identifier_prop id }.
Proof.
  intros.
  unfold Well_Formed_Identifier_prop.
  apply Well_Formed_string_prop_dec.
Qed.

Definition Well_Formed_ps_qname_prop (ps : ps_qname) :=
  let (psname, name) := ps in
    Well_Formed_string_prop psname /\ Well_Formed_string_prop name.

Lemma Well_Formed_ps_qname_prop_dec: forall ps : ps_qname,
  { Well_Formed_ps_qname_prop ps } + { ~ Well_Formed_ps_qname_prop ps }.
Proof.
  intros.
  unfold Well_Formed_ps_qname_prop.
  destruct ps.
  apply dec_sumbool_and; apply Well_Formed_string_prop_dec.
Defined.

Definition Well_Formed_fq_name_prop (f : fq_name) :=
  let (path, name, impl_name) := f in
    All Well_Formed_Identifier_prop path /\
    Well_Formed_Identifier_prop name /\
    match impl_name with
    | None => True
    | Some s => Well_Formed_Identifier_prop s
    end.

Lemma Well_Formed_fq_name_prop_dec: forall f: fq_name,
  { Well_Formed_fq_name_prop f } + { ~ Well_Formed_fq_name_prop f }.
Proof.
  intros.
  unfold Well_Formed_fq_name_prop.
  destruct f.
  apply dec_sumbool_and.
  - apply sumbool_All_dec; apply Well_Formed_Identifier_prop_dec.
  - apply dec_sumbool_and.
    * apply Well_Formed_Identifier_prop_dec.
    * destruct impl_name. apply Well_Formed_Identifier_prop_dec. auto.
Defined.

(** [split_fq_colons] and [split_fq_dot] are helper functions for parsing strings that contain a fully qualitied name in the form "A::B::C.D" *)

Fixpoint split_fq_colons (path : list identifier) (pending : string) (s : string) (after_dot : option identifier) :=
  match s with
  | EmptyString => (FQN path (Id pending) after_dot)
  | String ":" (String ":" tail) => split_fq_colons (path ++ (cons (Id pending) nil)) EmptyString tail after_dot
  | String " " tail => split_fq_colons path pending tail after_dot
  | String head tail => split_fq_colons path (pending ++ (String head EmptyString)) tail after_dot
  end.

Fixpoint split_fq_dot (pending : string) (s : string) :=
  match s with
  | EmptyString => split_fq_colons nil EmptyString pending None
  | String "." tail => split_fq_colons nil EmptyString pending (Some (Id tail))
  | String head tail => split_fq_dot (pending ++ (String head EmptyString)) tail
  end.

(** [parse_fq_name] parses the input string and returns a fully qualified name *)

Definition parse_fq_name (s : string) : fq_name := split_fq_dot EmptyString s.

(** [parse_ps_qname] parses the input string and returns a property set qualified name *)
Definition parse_psq_name (s: string) : ps_qname :=
  let (path, name, _) := parse_fq_name (s) in
  match path with
  | h :: nil => PSQN (h->toString) (name->toString)
  | nil => PSQN "" (name->toString)
  | _ => empty_ps_qname
  end.

(** [parse_feature_ref_name] parses the input string and returns a feautre reference name *)
Definition parse_feature_ref_name (s : string) : feature_ref :=
  let (path, name, f) := parse_fq_name (s) in
  match path with
  | nil =>
      match f with
      | Some id => FREF (name->toString) (id->toString)
      | None => FREF (name->toString) EmptyString
      end
  | _ => empty_feature_ref
  end.

Class Element_id A : Type := {
  get_id : A -> identifier ; (* Id *) }.

Notation "c '->id' " := (get_id c)
  (at level 80, right associativity).
