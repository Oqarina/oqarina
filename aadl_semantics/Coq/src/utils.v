(** %\chapter{utils.v -- Additional definition }% *)

From Coq Require Import List.
Require Import Coq.Logic.Decidable.

Set Implicit Arguments.

(** Additional definition of utility functions. *)

(** * All *)

(** We define a variant of All that matches the types used when defining our induction principles.
See %\S 3.8% from %\cite{DBLP:books/daglib/0035083}% for more details
*)

Section All.

    Variable T : Set.
    Variable P : T -> Prop.

    Fixpoint All (ls : list T) : Prop :=
      match ls with
        | nil => True
        | h :: t => P h /\ All t
      end.

    Hypothesis HP : forall t : T, decidable (P t).

    Lemma All_dec: forall lt : list T, decidable(All lt).
    Proof.
      induction lt.
      - unfold All. apply dec_True. (* from Coq.Logic.Decidable *)
      - simpl. apply dec_and. (* from Coq.Logic.Decidable *)
        * apply HP.
        * apply IHlt.
    Qed.

End All.