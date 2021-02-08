(** %\chapter{utils.v -- Additional definition }% *)

(* begin hide *)
From Coq Require Import List.
Require Import Coq.Logic.Decidable.

Set Implicit Arguments.
(* end hide *)

(** Additional definition of utility functions. *)

(** * All *)

(** We define a variant of %\coqdocvar{All}% that matches the types used when
defining our induction principles. See %\S 3.8% from %\cite{DBLP:books/daglib/0035083}% for more details
*)

(* begin hide *)
Section All.
(* end hide *)

    Variable T : Set.
    Variable P : T -> Prop.

    Fixpoint All (ls : list T) : Prop :=
      match ls with
        | nil => True
        | h :: t => P h /\ All t
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

(* begin hide*)
End All.
(* end hide *)