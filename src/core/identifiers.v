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
Require Import Oqarina.coq_utils.utils.

Section ASCII_Helpers.

  (* The following adds basic string manipulation functions. We might consider moving them in a separate file. *)

  Definition ascii_eqb c c' := (N_of_ascii c =? N_of_ascii c')%N.
  Definition ascii_leb c c' := (N_of_ascii c <=? N_of_ascii c')%N.

  Infix "<=?" := ascii_leb : char_scope.
  Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

  Definition is_alpha c :=
    ((("a" <=? c) && (c <=? "z")) ||
    (("A" <=? c) && (c <=? "Z")) ||
    (c =? "_") ||
    (c =? "."))%char.

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

(** [parse_fq_name] parses the input string and returns a fully qualified name*)

Definition parse_fq_name (s : string) : fq_name := split_fq_dot EmptyString s.

(* begin hide *)
  Example test_split_fq_colons_1 :
    split_fq_colons nil EmptyString "Hello" None = FQN nil (Id "Hello") None.
  Proof.
    trivial.
  Qed.

  Example test_split_fq_colons_2:
    split_fq_colons nil EmptyString "Hello::World" None = FQN (Id "Hello" :: nil) (Id "World") None.
  Proof.
    trivial.
  Qed.

  Example test_split_fq_colons_3:
    split_fq_colons nil EmptyString "A::B::C::D" None = FQN (Id "A" :: Id "B" :: Id "C" :: nil) (Id "D") None.
  Proof.
    trivial.
  Qed.

  Example test_split_fq_colons_4:
    split_fq_colons nil EmptyString "" None = FQN nil (Id "") None.
  Proof.
    trivial.
  Qed.

  Example test_parse_fq_name_1 : parse_fq_name "Foo.impl" = FQN nil (Id "Foo") (Some (Id "impl")).
  Proof.
    trivial.
  Qed.

  Example test_parse_fq_name_2 : parse_fq_name "Foo::Bar.impl" = FQN (Id "Foo" :: nil) (Id "Bar") (Some (Id "impl")).
  Proof.
    trivial.
  Qed.
  (* end hide *)
