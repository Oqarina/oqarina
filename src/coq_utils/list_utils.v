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
(* begin hide *)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Coq.Logic.Decidable.
Set Implicit Arguments.
(* end hide *)

(** * All *)

(** We define a variant of %\coqdocvar{All}% that matches the types used when defining our induction principles. See %\S 3.8% from %\cite{DBLP:books/daglib/0035083}% for more details. *)

(* begin hide *)
Section All.
(* end hide *)

    Variable T : Type.
    Variable P : T -> Prop.

    Fixpoint All (ls : list T) : Prop :=
      match ls with
        | nil => True
        | h :: t => P h /\ All t
      end.

    Fixpoint All_Or (ls : list T) : Prop :=
      match ls with
        | nil => False
        | h :: t => P h \/ All_Or t
      end.

    (** We show that if %\coqdocvar{HP}% holds, then %\coqdocvar{All}%
        is decidable as well.*)

    Hypothesis HP : forall t : T, decidable (P t).

    Lemma All_dec: forall lt : list T, decidable(All lt).
    Proof.
      induction lt.
      - unfold All. apply dec_True. (* from Coq.Logic.Decidable *)
      - simpl. apply dec_and. (* from Coq.Logic.Decidable *)
        * apply HP.
        * apply IHlt.
    Qed.

    Lemma All_Or_dec: forall lt : list T, decidable(All_Or lt).
    Proof.
      induction lt.
      - unfold All_Or. apply dec_False. (* from Coq.Logic.Decidable *)
      - simpl. apply dec_or. (* from Coq.Logic.Decidable *)
        * apply HP.
        * apply IHlt.
    Qed.

(* begin hide*)
End All.
(* end hide *)

Section BoolList.

    (** [andbl] returns the logical and of a list of bools *)

    Fixpoint andbl (lb : list bool) :=
        match lb with
            | nil => true
            | h :: t => andb h (andbl t)
        end.

End BoolList.

Section NatList.

  (** [list_min] returns the minumum value of a list *)

  Definition list_min (l : list nat) :=
    match l with
    | [] => 0
    | h :: t => fold_left (fun acc x => min acc x) l h
    end.

  (** [list_max] returns the maximum value of a list *)

  Definition list_max (l : list nat) :=
    match l with
    | [] => 0
    | h :: t => fold_left (fun acc x => max acc x) l h
    end.

End NatList.

Section GenericLists.

  (** [clean_options] turns option elements of [l] into a non-option type, removing all occurences of [None] *)

  Variable T : Type.

  Fixpoint clean_options (l : list (option T)) :=
    match l with
    | [] => []
    | h :: t => match h with
                | None => clean_options t
                | Some h' => h' :: clean_options t
                end
    end.

  Lemma not_in_car (x a : T): ~ In x [a] <-> x<>a.
  Proof.
    simpl. intuition.
  Qed.

End GenericLists.
