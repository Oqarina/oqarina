(** %\chapter{utils.v -- Additional definition }% *)

(* begin hide *)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Coq.Logic.Decidable.

Set Implicit Arguments.
(* end hide *)

(** Additional definition of utility functions. *)

(** * All *)

(** We define a variant of %\coqdocvar{All}% that matches the types used when defining our induction principles. See %\S 3.8% from %\cite{DBLP:books/daglib/0035083}% for more details. *)

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

Section Definitions.
(* end hide *)

  (** The following defines a shortcut to use sumbool-based definition for decidability. See %\cite{appel2018software}%, chapter "Programming with Decision Procedures" for details. *)

  Variable A : Prop.
  Definition dec_sumbool := { A } + { ~ A }.
  Definition eq_dec T := forall x y : T, {x=y}+{x<>y}.

  Definition eq_dec_Prop (P : Prop) := { P } + { ~P }.

  Definition Oracle (P : Prop) (eq_dec : eq_dec_Prop P): bool :=
    match (eq_dec) with
      | left _ => true
      | right _ => false
    end.

(* begin hide *)
End Definitions.

Section Predicates.
(* end hide *)

  Variable A : Prop.
  Hypothesis HA : { A } + {~ A}.

  Variable B : Prop.
  Hypothesis HB : { B } + {~ B}.

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
      unfold dec_sumbool.
      destruct HA.
      - right. auto.
      - left. auto.
  Defined.

  Lemma eq_dec_decidable T (x y:T) : {x=y}+{x<>y} -> x = y \/ x <> y.
  Proof.
    intros.
    destruct H.
    - left. apply e.
    - right. apply n.
  Defined.

(* begin hide *)
End Predicates.

Section Lists.
(* end hide *)
  Variable T : Set.
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

End Decidability.
(* end hide *)

(** ** Helper functions to build a boolean equality from a decidable equality. *)

(* begin hide *)
Section EqEqb.
(* end hide *)

  Variable T : Type.
  Variable HT : T -> Prop.
  Hypothesis T_Prop_dec : forall t : T, { HT t} + {~ HT t}.

  Fixpoint filter_dec (l:list T) : list T :=
    match l with
     | nil => nil
     | h :: t => match T_Prop_dec h with
                | left _ => h::(filter_dec t)
                | right _ => filter_dec t
                end
    end.

  Definition eq (x : T) (y : T) := { x = y } + { x <> y }.
  Hypothesis eq_dec' : forall x y : T, eq x y.

  Definition eqdec2eqb (x : T) (y : T) : bool :=
    match eq_dec' x y with
    | left _ => true
    | right _ => false
    end.

  Lemma eqb_eq : forall x y, eqdec2eqb x y = true <-> x = y.
  Proof.
    intros x y. unfold eqdec2eqb. destruct eq_dec' as [EQ|NEQ].
    - auto with *.
    - split.
      + discriminate.
      + intro EQ; elim NEQ; auto.
  Qed.

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
