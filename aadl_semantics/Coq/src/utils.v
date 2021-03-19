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

(** * Some lemma on decidability using [sumbool]*)

(* begin hide*)
Section Decidability.
(* end hide *)

  (** The following defines a shortcut to use sumbool-based definition for decidability. See %\cite{appel2018software}%, chapter "Programming with Decision Procedures" for details. *)

  Definition eq_dec T := forall x y:T, {x=y}+{x<>y}.

  Variable A : Prop.
  Hypothesis HA : { A } + {~ A}.

  Variable B : Prop.
  Hypothesis HB : { B } + {~ B}.

  Lemma dec_sumbool_and:  { A /\ B  } + { ~ (A /\ B)}.
  Proof.
      unfold eq_dec.
      destruct HA , HB ;
      auto ||
      right; intuition.
  Qed.

  Lemma eq_dec_decidable (T: Type) (x y:T) : {x=y}+{x<>y} -> x = y \/ x <> y.
  Proof.
    intros.
    destruct H.
    - left. apply e.
    - right. apply n.
  Qed.

(*
  Lemma decidable_eq_dec T : forall x y:T,  x = y \/ x <> y -> {x=y}+{x<>y}.
  Proof.
    intros.
    -
    destruct H.
    - left. apply H.
*)


(* begin hide *)
End Decidability.
(* end hide *)