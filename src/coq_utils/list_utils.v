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
