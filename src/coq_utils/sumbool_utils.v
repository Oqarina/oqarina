(** * Some lemma on decidability using [sumbool]*)
Require Import Oqarina.coq_utils.list_utils.
(* begin hide *)
Section Sumbool_Decidability.
(* end hide *)

  (** The following defines a shortcut to use sumbool-based definition for decidability. See %\cite{appel2018software}%, chapter "Programming with Decision Procedures" for details. *)

  Variable A : Prop.
  Hypothesis HA : { A } + {~ A}.

  Variable B : Prop.
  Hypothesis HB : { B } + {~ B}.

  Definition dec_sumbool (P : Prop) := { P } + { ~ P }.

  Lemma dec_sumbool_and:  { A /\ B  } + { ~ (A /\ B) }.
  Proof.
      destruct HA , HB ;
        auto ||
        right; intuition.
  Defined.

  Lemma dec_sumbool_or:  { A \/ B  } + { ~ (A \/ B) }.
  Proof.
      destruct HA , HB ;
        auto ||
        right; intuition.
  Defined.

  Lemma dec_sumbool_not: dec_sumbool ( ~ A ).
  Proof.
      destruct HA.
      - right. auto.
      - left. auto.
  Defined.

(* begin hide *)
End Sumbool_Decidability.

Section Lists.
(* end hide *)
  Variable T : Type.
  Variable P : T -> Prop.
  Hypothesis HP' : forall t : T, {P t} + {~ P t}.

  Lemma sumbool_All_dec (l : list T): { All P l } + {~ All P l}.
  Proof.
    induction l.
    - unfold All. auto.
    - simpl. apply dec_sumbool_and.
      * apply HP'.
      * apply IHl.
  Qed.

(* begin hide *)
End Lists.
(* end hide *)