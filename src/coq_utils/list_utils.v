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
Require Import Coq.Bool.Bool.
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

  Lemma All_Forall l :
    All l <-> Forall P l.
  Proof.
    induction l; simpl; split; intros HF; try now inversion HF; intuition.
  Qed.

  Lemma All_left_cons : forall (a: T) (lt : list T),
      All (a :: lt) <-> P a /\ All lt.
  Proof.
    simpl. intuition.
  Qed.

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

    Lemma All_In :
      forall (l : list T),
        (forall x, In x l -> P x) <-> All l.
    Proof.
      intros.
      split.
      induction l.
      + intros. simpl ; auto.
      + intros. simpl. split. apply H. apply in_eq.
        apply IHl. intros. apply H. right. apply H0.
      + intros H. induction l.
        - intros. simpl. induction H0.
        - intros. simpl. destruct H0 as [H1 | ]. destruct H as [H2 H3].
          rewrite <- H1. assumption. destruct H as [H2 H3]. apply IHl ; auto.
    Qed.

(* begin hide*)
End All.
(* end hide *)

Section FoldLeft.
  Variable A B : Type.
  Implicit Types x : B.
  Implicit Types l : list B.
  Variables (f : A -> B -> A) (i : A).

  Lemma fold_left_nil :
    fold_left f nil i = i.
  Proof. auto. Qed.

  Lemma fold_left_cons : forall x l,
    fold_left f (x::l) i = fold_left f l (f i x).
  Proof. auto. Qed.

End FoldLeft.

Section BoolList.

    (** [andbl] returns the logical and of a list of bools *)

    Definition andbl (lb : list bool) :=
      fold_left andb lb true.

    Lemma andbl_true : forall (l : list bool),
      andbl (true :: l) = andbl l.
    Proof.
      intros.
      induction l.
      - trivial.
      - unfold andbl. rewrite fold_left_cons. simpl. auto.
    Qed.

    Lemma andbl_false : forall (l : list bool),
      andbl (false :: l) = false.
    Proof.
      intros.
      induction l.
      - trivial.
      - unfold andbl. rewrite fold_left_cons. simpl. auto.
    Qed.

    Lemma andbl_concatenate: forall (b : bool) (l : list bool) ,
      andbl [b ; andbl l] = andbl (b :: l).
    Proof.
      intros.
      induction l ; unfold andbl ; simpl ; destruct b ; auto.
    Qed.

    Lemma andbl_singleton: forall (b : bool),
      andbl [ b ] = b.
    Proof.
      trivial.
    Qed.

    Definition orbl (lb : list bool) :=
      fold_left orb lb false.

    Lemma orbl_true : forall (l : list bool),
      orbl (true :: l) = true.
    Proof.
      intros.
      induction l.
      - trivial.
      - unfold orbl. rewrite fold_left_cons. simpl. apply IHl.
    Qed.

    Lemma orbl_false : forall (l : list bool),
        orbl (false :: l) = orbl l.
    Proof.
      intros.
      induction l.
      - trivial.
      - unfold orbl. rewrite fold_left_cons. simpl. auto.
    Qed.

    Lemma orbl_app : forall (l1 l2: list bool),
      orbl (l1 ++ l2) = orbl (orbl l1 :: l2).
    Proof.
      intros.
      unfold orbl.
      apply fold_left_app.
    Qed.

  Lemma orbl_concatenate: forall (b : bool) (l : list bool) ,
    orbl [b ; orbl l] = orbl (b :: l).
  Proof.
    intros.
    induction l.
    - unfold orbl. simpl. destruct b ; auto.
    - unfold orbl. simpl. destruct b ; auto.
  Qed.

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

  Fixpoint to_option (l : list T) : list (option T) :=
    match l with
    | [] => []
    | h :: t => Some h :: to_option t
    end.

  Fixpoint has_none (l : list (option T)) :=
    match l with
      | [] => false
      | h :: t => match h with
                  | None => true
                  | Some _ => has_none t
                  end
    end.

  Lemma has_none_None: has_none [ None ] = true.
  Proof. auto. Qed.

  Lemma has_none_Some: forall (t : T) (l : list (option T)),
    has_none ((Some t) :: l) = has_none l.
  Proof.
    simpl ; reflexivity.
  Qed.

  Definition is_nil (l : list T) : bool :=
    match l with
    | nil => true
    | _ => false
    end.

  Lemma not_in_car (x a : T): ~ In x [a] <-> x<>a.
  Proof.
    simpl. intuition.
  Qed.

(*| :coq:`map2` is equivalent to the default :coq:`map` that applies a function to each element, but of two lists. |*)

  Variables (A : Type) (B : Type) (C : Type).
  Variable f : A -> B -> C.

  Fixpoint map2 (l:list A) (l2:list B) : list C :=
      match l, l2 with
          | a :: t, b :: t' => (f a b) :: (map2 t t')
          | _, _ => []
      end.

(*| :coq:`filter2` is equivalent to the default :coq:`filter` that filters
 elements of a list.  |*)

  Variable g : A -> B -> bool.

  Fixpoint filter2 (l:list A) (l2:list B) : list (A * B) :=
      match l, l2 with
          | a :: t, b :: t' => if (g a b) then
                                  (a, b) :: (filter2 t t') else (filter2 t t')
          | _, _ => []
      end.

End GenericLists.

Section in_boolean.

  Variable A : Type.
  Variable beq: A -> A -> bool.

  Variable H: forall t1 t2, reflect (t1 = t2) (beq t1 t2).

  Fixpoint In_b (x: A) (l: list A) : bool :=
    match l with
      | [] => false
      | h :: t => orb (beq h x) (In_b x t)
    end.

  Theorem In_reflect (x: A) (L: list A) : reflect (In x L) (In_b x L).
  Proof.
    induction L.
    + simpl. apply ReflectF. auto.
    + simpl. destruct (H a x).
      - subst. assert (beq x x = true). destruct (H x x); auto. simpl.
        apply ReflectT. left. auto.
      - destruct IHL.
        * apply ReflectT. auto.
        * assert (beq x a = false). destruct (H x a); congruence.
          apply ReflectF. tauto.
  Qed.

End in_boolean.
