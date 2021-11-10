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
(** %\chapter{utils.v -- Additional definition }% *)

(* begin hide *)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)

Require Import Oqarina.coq_utils.sumbool_utils.
Set Implicit Arguments.
(* end hide *)

(** Additional definition of utility functions. *)

(* begin hide*)
Section Definitions.
(* end hide *)

  Definition eq_dec T := forall x y : T, {x=y}+{x<>y}.

  Definition Oracle (P : Prop) (P_dec : dec_sumbool P): bool :=
    match (P_dec) with
      | left _ => true
      | right _ => false
    end.

(* begin hide *)
End Definitions.

(* begin hide *)
Section EqEqb.
(* end hide *)

  Variable T : Type.
  Variable HT : T -> Prop.
  Hypothesis T_Prop_dec : forall t : T, { HT t } + { ~ HT t }.

  Fixpoint filter_dec (l:list T) : list T :=
    match l with
     | nil => nil
     | h :: t => match T_Prop_dec h with
                | left _ => h::(filter_dec t)
                | right _ => filter_dec t
                end
    end.

(* begin hide *)
End EqEqb.

Section Lists_Misc.

  Variables (A:Type)(dec : forall x y:A, {x=y}+{x<>y}).

  Definition In_dec := List.In_dec dec. (* Already in List.v *)
(* end hide *)

(** * Additional definitions for lists *)

  (** The following duplicates the proof of [NoDup_dec]. This is required since we need a non-opaque (i.e. terminated by [Defined] proof). See https://github.com/coq/coq/issues/14149. *)

  Lemma NoDup_dec' (l:list A) : {NoDup l}+{~NoDup l}.
  Proof.
    induction l as [|a l IH].
    - left; now constructor.
    - destruct (In_dec a l).
      + right. inversion_clear 1. tauto.
      + destruct IH.
        * left. now constructor.
        * right. inversion_clear 1. tauto.
  Defined.

(** [list_alter] apply [f] on the pos-th element of [l] *)

Fixpoint list_alter {A} (pos : nat) (l: list A) (f : A -> A) :=
  match l with
  | [] => []
  | x :: l => match pos with
                | 0 => f x :: l
                | S i => x :: list_alter i l f
              end
  end.

(* begin hide *)
End Lists_Misc.
(* end hide *)
