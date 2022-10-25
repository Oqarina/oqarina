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
Require Import Coq.ssr.ssrbool.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Lia.

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
      - unfold All. apply Decidable.dec_True. (* from Coq.Logic.Decidable *)
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

  Theorem In_In_b (x: A) (L: list A) : In x L -> In_b x L = true.
  Proof.
    eapply (introT (In_reflect x L)).
  Qed.

  Definition NoDup_bool (L: list A): bool.
  Proof.
    induction L.
    + exact true.
    + exact (negb (In_b a L) && IHL).
  Defined.

  Theorem NoDup_reflect (L: list A) : reflect (NoDup L) (NoDup_bool L).
  Proof.
    induction L.
    + simpl. apply ReflectT. apply NoDup_nil.
    + simpl. destruct (In_reflect a L).
      - simpl. apply ReflectF. intro. apply NoDup_cons_iff in H0. intuition.
      - simpl. destruct IHL.
        * apply ReflectT. apply NoDup_cons; auto.
        * apply ReflectF. intro. apply NoDup_cons_iff in H0. intuition.
  Defined.

  Definition inclb (l1 l2: list A) : bool :=
    forallb (fun x => In_b x l2) l1.

  Definition foo: forall (a: A) (l1 l2: list A),
    In a l2 -> incl (a :: l1) l2 <-> incl l1 l2.
  Proof.
    intros.
    split.
    - intros. apply incl_cons_inv in H1. intuition.
    - intros. apply incl_cons ; auto.
  Qed.

  Theorem incl_reflect (l1 l2: list A) :
    reflect (incl l1 l2) (inclb l1 l2).
  Proof.
    apply (iffP idP).
    - induction l1.
      + intuition. simpl. intros. apply incl_nil_l.
      + simpl. intros. apply andb_true_iff in H0. destruct H0.
        apply incl_cons.
        * eapply (elimT (In_reflect a l2)) in H0. apply H0.
        * apply IHl1, H1.
    - induction l1.
      + intuition.
      + simpl. intros. apply incl_cons_inv in H0. destruct H0.
        apply andb_true_iff. split.
        * apply (introT (In_reflect a l2)) in H0. apply H0.
        * apply IHl1, H1.
  Qed.

End in_boolean.

Section incl_split.

  Variable A : Type.

  (*| :coq:`NoDup_incl_split` extends Coq's standard library :coq:`in_split` to the case of lists. |*)

  Lemma incl_split: forall (l1 l2 : list A),
    NoDup l1 -> incl l1 l2 ->
      exists comp, Permutation (l1 ++ comp) l2.
  Proof.
    intros l1.
    induction l1 as [| x xs IH]; intros l2 nodup_l1 incl_l1_l2.

    - (* l2 is an obvious solution *)
      exists l2 ; simpl ; apply Permutation_refl.

    - (* Ths general idea is to build a complement to `incl (x::xs) l2`.
      For that, we have to rely on `in_split` only .. *)

      (* First, we show that x in obviously in l2 .. *)
      assert (x_in_l2: In x l2).
      apply (incl_l1_l2 x). apply in_eq.

      (* then we apply in_split to build complements .. *)
      destruct (in_split _ _ x_in_l2) as [pref [comp]]. subst.
      inversion nodup_l1; subst.

      (* because of x_in_l2, one can deduce that xs is included
        in `pref ++ comp`. *)
      assert (incl xs (pref ++ comp)).
      unfold incl.
      intros a a_in.
      apply in_or_app.
      apply (incl_app_inv [x] xs) in incl_l1_l2.
      destruct incl_l1_l2 as [incl_x incl_xs].
      specialize (incl_xs a a_in).
      apply in_app_or in incl_xs.
      destruct incl_xs as [in_pref | [in_x | in_comp]]; intuition.
      contradict a_in. subst. intuition.

      (* We combine the previous hypotheses with IH to build a
        candidate. *)
      destruct (IH _ H2 H) as [comp' perm_comp'].
      exists comp'.

      (* From here, we massage the final permutation to conclude *)
      simpl.
      rewrite Permutation_middle.

      rewrite Permutation_sym
        with  (l := xs ++ x :: comp') (l' := pref ++ x :: comp).
      apply Permutation_refl.
      apply Permutation_elt, perm_comp'.
  Qed.


End incl_split.

Section nodup.

  Variable A : Type.
  Hypothesis A_eq_dec: forall x y : A, {x = y} + {x <> y}.

  Variable beq: A -> A -> bool.

  Variable H: forall t1 t2, reflect (t1 = t2) (beq t1 t2).

  Lemma In_nodup: forall (b: A) (l : list A),
    In b l -> nodup A_eq_dec (b :: l) = nodup A_eq_dec l.
  Proof.
    intros.
    simpl.
    destruct (in_dec A_eq_dec b l).
    - reflexivity.
    - contradiction.
  Qed.

  Lemma nodup_not_in: forall (a: A) (l : list A),
    ~ In a l -> nodup A_eq_dec (a :: l) = a :: nodup A_eq_dec l.
  Proof.
    intros.
    simpl.
    destruct (in_dec A_eq_dec a l).
    - contradiction.
    - reflexivity.
  Qed.

  Fixpoint nodupb (l : list A) : list A :=
    match l with
    | [] => []
    | h :: t => if In_b beq h t then nodupb t else h :: nodupb t
    end.

  Lemma In_nodupb: forall (b: A) (l : list A),
    In_b beq b l = true -> nodupb (b :: l) = nodupb l.
  Proof.
    intros.
    simpl.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma nodupb_not_inb: forall (a: A) (l : list A),
    In_b beq a l = false -> nodupb (a :: l) = a :: nodupb l.
  Proof.
    intros.
    simpl.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma nodupb_sound: forall l,
    nodupb l = nodup A_eq_dec l.
  Proof.
    intros.
    induction l.
    - simpl ; reflexivity.
    - destruct (in_dec A_eq_dec a l) eqn:in_dec;
      destruct (In_b beq a l) eqn:Inb.
      * destruct (In_nodup _ l i).
        destruct (In_nodupb _ l Inb). auto.
      * eapply (elimF (In_reflect  _ H a l)) in Inb. contradiction.
      * eapply (elimT (In_reflect  _ H a l)) in Inb. contradiction.
      * assert (nodup A_eq_dec (a :: l) = a :: nodup A_eq_dec l).
        destruct (nodup_not_in _ l n) ; auto.
        assert (nodupb (a :: l) = a :: nodupb l).
        destruct (nodupb_not_inb _ l Inb) ; auto.
        rewrite H0, H1, IHl. reflexivity.
  Qed.

End nodup.

Section BoolExt.

Lemma orb_middle: forall a b c,
  a || b || c = b || a || c.
Proof.
  intros.
  destruct a, b, c ; simpl ; reflexivity.
Qed.

End BoolExt.

Section BoolList.

  (** [andbl] returns the logical and of a list of bools *)

  Definition andbl (lb : list bool) :=
      fold_left andb lb true.

    Lemma andbl_empty: andbl [ ] = true.
    Proof. trivial. Qed.

    Lemma andbl_singleton: forall (b : bool),
      andbl [ b ] = b.
    Proof. trivial. Qed.

    Lemma andbl_red: forall (b: bool) (l : list bool),
      andbl (b :: l) = andb b (andbl l).
    Proof.
      intros.
      unfold andbl.
      rewrite fold_left_cons.
      rewrite andb_true_l.
      case b.
      - simpl. reflexivity.
      - simpl. induction l. simpl ; reflexivity. rewrite fold_left_cons, andb_false_l. apply IHl.
    Qed.

    Lemma In_andbl: forall (b: bool) (l : list bool),
      In b l -> andbl (b :: l) = andbl l.
    Proof.
      intros.
      induction l.
      - simpl. contradiction.
      - destruct H.
        * repeat rewrite andbl_red. subst. case b ; trivial.
        * repeat rewrite andbl_red. case a.
          + rewrite andb_true_l. rewrite <- andbl_red. generalize H. apply IHl.
          + rewrite andb_false_l, andb_false_r. reflexivity.
    Qed.

    Lemma andbl_nodup: forall (l : list bool),
      andbl l = andbl (nodup bool_dec l).
    Proof.
      intros.
      induction l.
      - trivial.
      - generalize (in_dec bool_dec a l).
        intros.
        destruct H.
        * rewrite In_nodup. rewrite In_andbl. apply IHl. apply i. apply i.
        * rewrite nodup_not_in. repeat rewrite andbl_red. rewrite IHl. reflexivity. auto.
    Qed.

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

    Lemma andbl_cons: forall b l, andbl (b::l) = andb b (andbl l).
    Proof.
      intros.
      unfold andbl.
      simpl.
      destruct b.
      - rewrite andb_true_l ; intuition.
      - rewrite andb_false_l. induction l. intuition. rewrite fold_left_cons.
        rewrite andb_false_l. apply IHl.
    Qed.

    Lemma andbl_app : forall (l1 l2: list bool),
      andbl (l1 ++ l2) = andbl (andbl l1 :: l2).
    Proof.
      intros.
      unfold andbl.
      apply fold_left_app.
    Qed.

    Lemma andbl_split: forall (l1 l2: list bool),
      andbl (l1 ++ l2) = andb (andbl l1) (andbl l2).
    Proof.
      intros.
      induction l1.
      - intuition.
      - destruct a.
        * rewrite andbl_app. rewrite andbl_true.
        rewrite <- andbl_app. apply IHl1.
        * rewrite andbl_app. repeat rewrite andbl_false. rewrite andb_false_l. reflexivity.
    Qed.

    Lemma andbl_cons2: forall a b l,
      andbl (a::b::l) = andb (andbl [ a ; b ]) (andbl l).
    Proof.
      intros.
      rewrite <- andbl_split.
      auto.
    Qed.

    Lemma andbl_permut: forall (l1 l2: list bool),
      Permutation l1 l2 -> andbl l1 = andbl l2.
    Proof.
        apply Permutation_ind_bis.
        - auto.
        - intros. repeat rewrite andbl_cons. rewrite H0. auto.
        - intros.
          rewrite andbl_cons2.
          rewrite H0.
          assert (andbl [y;x] = andbl [x;y]).
          + unfold andbl. simpl. apply andb_comm.
          + rewrite H1. rewrite <- andbl_cons2. reflexivity.
        - intros. rewrite H0. auto.
    Qed.

    Definition orbl (lb : list bool) :=
      fold_left orb lb false.

    Lemma orbl_singleton: forall (b : bool),
      orbl [ b ] = b.
    Proof. trivial. Qed.

    Lemma orbl_true : forall (l : list bool),
      orbl (true :: l) = true.
    Proof.
      intros.
      induction l.
      - trivial.
      - unfold orbl. rewrite fold_left_cons. simpl. apply IHl.
    Qed.

    Lemma orbl_nil: orbl [] = false.
    Proof. intuition. Qed.

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

  Lemma orbl_red: forall (b: bool) (l : list bool),
    orbl (b :: l) = orb b (orbl l).
  Proof.
    intros.
    unfold orbl.
    rewrite fold_left_cons.
    rewrite orb_false_l.
    case b.
    - simpl.  induction l. simpl ; reflexivity. rewrite fold_left_cons, orb_true_l. apply IHl.
    - simpl ; reflexivity.
  Qed.

  Lemma orbl_split: forall (l1 l2: list bool),
    orbl (l1 ++ l2) = orb (orbl l1) (orbl l2).
  Proof.
    intros.
    induction l1.
    - intuition.
    - destruct a.
      * rewrite orbl_app. repeat rewrite orbl_true.
        rewrite orb_true_l ; reflexivity.
      * rewrite orbl_app. repeat rewrite orbl_false. rewrite <- orbl_app. apply IHl1.
  Qed.

  Lemma orbl_cons: forall b l, orbl (b::l) = orb b (orbl l).
  Proof.
    intros.
    unfold orbl.
    simpl.
    destruct b.
    - rewrite orb_true_l.
      induction l ; intuition.
    - rewrite orb_false_l ; reflexivity.
  Qed.

  Lemma orbl_cons2: forall a b l,
    orbl (a::b::l) = orb (orbl [ a ; b ]) (orbl l).
  Proof.
    intros.
    rewrite <- orbl_split.
    auto.
  Qed.

  Lemma In_orbl: forall (b: bool) (l : list bool),
    In b l -> orbl (b :: l) = orbl l.
  Proof.
  intros.
  induction l.
  - simpl. contradiction.
  - destruct H.
    * subst. case b ; trivial.
    * case a.
      + repeat rewrite orbl_red. repeat rewrite orb_true_l. rewrite orb_true_r ; reflexivity.
      + repeat rewrite orbl_red. repeat rewrite orb_false_l. rewrite <- orbl_red. apply IHl, H.
  Qed.

  Lemma orbl_permut: forall (l1 l2: list bool),
    Permutation l1 l2 -> orbl l1 = orbl l2.
  Proof.
      apply Permutation_ind_bis.
      - auto.
      - intros. repeat rewrite orbl_cons. rewrite H0. auto.
      - intros.
        rewrite orbl_cons2.
        rewrite H0.
        assert (orbl [y;x] = orbl [x;y]).
        + unfold orbl. simpl. apply orb_comm.
        + rewrite H1. rewrite <- orbl_cons2. reflexivity.
      - intros. rewrite H0. auto.
  Qed.

  Lemma orbl_nodup: forall (l : list bool),
    orbl l = orbl (nodup bool_dec l).
  Proof.
  intros.
  induction l.
  - trivial.
  - generalize (in_dec bool_dec a l).
    intros.
    destruct H.
    * rewrite In_nodup. rewrite In_orbl. apply IHl. apply i. apply i.
    * rewrite nodup_not_in. repeat rewrite orbl_red. rewrite IHl. reflexivity. auto.
  Qed.

  Lemma absorption_orbl: forall (l1 l2: list bool),
    NoDup l1 -> incl l1 l2 -> andbl l1 = orb (andbl l1) (andbl (l2)).
  Proof.
    intros.
    destruct (incl_split H H0).
    destruct (andbl_permut H1).
    repeat rewrite andbl_split.
    rewrite absorption_orb.
    reflexivity.
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

  Lemma app_not_nil: forall (l1 l2: list T),
    l1 <> [] -> l2 <> [] -> l1 ++ l2 <> [].
  Proof.
    intros.
    unfold app.
    destruct l1.
    apply H0.
    intuition.
    apply eq_sym in H1.
    apply nil_cons in H1.
    intuition.
  Qed.

  Lemma not_in_in: forall (x y: T) (l: list T),
    ~ In x l -> In y l -> x <> y.
  Proof.
    intros.
    induction l.
    - contradiction.
    - apply not_in_cons in H. destruct H. destruct H0.
      + subst. apply H.
      + apply IHl. apply H1. apply H0.
  Qed.

  Lemma length_S: forall (a: T) (l : list T),
    length (a :: l) = S (length l).
  Proof.
    auto.
  Qed.

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

  Lemma has_none_None2: forall (t : T) (l : list (option T)),
    has_none ((None) :: l) = true.
  Proof.
    simpl ; reflexivity.
  Qed.

  Lemma has_none_cons: forall (x : option T) (l : list (option T)),
    has_none (x :: l) = (has_none [ x ]) ||  (has_none l).
  Proof.
    intros.
    destruct x ; simpl ; auto.
  Qed.

  Lemma has_none_forall: forall (l : list (option T)),
    (forall  (x : option T), In x l -> (exists t, x = Some t)) -> has_none l = false.
  Proof.
    intros.
    induction l.
    - intuition.
    - rewrite has_none_cons.

      assert (forall (x: option T), In x l -> (exists t,x = Some t)).
      intros. apply H. apply in_cons. apply H0.

      assert (has_none l = false). apply IHl, H0.

      assert (exists t, a = Some t). apply H. apply in_eq.

      assert (has_none [a] = false).
      simpl. destruct H2. rewrite H2 ; reflexivity.

      (* conclusion *)
      rewrite H1, H3 ; intuition.
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

  Lemma in_map' :
    forall (l:list B) (x:A) (y : B),
      In y l -> In (f x y) (map (fun z => f x z) l).
  Proof.
    intro l; induction l; firstorder (subst; auto).
  Qed.

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

(*|
Generating sub-lists
--------------------

|*)

Section SubLists.

  Variable T : Type.

  (*| :coq:`sublists` generates all possible sublists of list l. |*)

  Fixpoint sublists (l : list T) :=
      match l with
          | [] => [[]]
          | h :: t => let l' := sublists t in
              map (fun x => h::x) l' ++ l'
      end.

  Lemma sublists_cons: forall a l,
    sublists (a::l) = map (fun x => a::x) (sublists l) ++ (sublists l).
  Proof.
    intuition.
  Qed.

  (*| :coq:`k_of_N` generates all sublists of size k of list l. |*)

  Definition k_of_N (k : nat) (l : list T) :=
      if Nat.eqb k 0 then [] else
      let subs := sublists l in
          filter (fun x => Nat.eqb (List.length x) k) subs.

Print k_of_N.

  Lemma k_of_N_nil: forall k, k_of_N k [] = [].
  Proof.
    intros.
    unfold k_of_N.
    destruct k ; compute ; reflexivity.
  Qed.

Lemma filter_lists_by_length_map_comm:
  forall k a l,
  filter (fun x : list T => Nat.eqb (length x) (S k))
    (map (fun x : list T => a :: x) l) =
    (map (fun x : list T => a :: x)
        (filter (fun x : list T => Nat.eqb (length x) k) l)).
Proof.
  intros.
  induction l.
  - intuition.
  - rewrite map_cons. simpl.
    destruct (Nat.eqb (length a0) k).
    + rewrite map_cons. rewrite IHl ; intuition.
    + apply IHl.
Qed.

Lemma k_of_N_cons: forall k a l, k > 1 ->
  k_of_N k (a::l) = ( map (fun x => a::x) (k_of_N (k-1) l)) ++ (k_of_N k l).
Proof.
  (* This proof is a mere rewriting of the various terms. *)

  intros.
  unfold k_of_N at 1. rewrite sublists_cons.
  rewrite filter_app.

  (* First, we reconstruct the "k_of_N k l" element*)
  assert (H1:
    (if Nat.eqb k 0
    then []
    else filter (fun x : list T => Nat.eqb (length x) k)
     (map (fun x : list T => a :: x) (sublists l)) ++
     filter (fun x : list T => Nat.eqb (length x) k) (sublists l))
    =
     if Nat.eqb k 0
     then []
     else filter (fun x : list T => Nat.eqb (length x) k)
      (map (fun x : list T => a :: x) (sublists l)) ++
    if Nat.eqb k 0
    then []
    else filter (fun x : list T => Nat.eqb (length x) k) (sublists l)).
  destruct k ; intuition.
  rewrite H1.

  assert(H2:
  (if Nat.eqb k 0
  then []
  else filter (fun x : list T => Nat.eqb (length x) k)
        (map (fun x : list T => a :: x) (sublists l)))
          = map (fun x : list T => a :: x) (k_of_N (k - 1) l)).
  destruct k eqn:k0.
  - intuition.
  - simpl.
    rewrite filter_lists_by_length_map_comm.
    unfold k_of_N. rewrite <- Arith_prebase.minus_n_O_stt.

    assert (Nat.eqb n 0 = false).
    apply PeanoNat.Nat.eqb_neq. lia.

    rewrite H0. reflexivity.

  - assert (Nat.eqb k 0 = false).
    apply PeanoNat.Nat.eqb_neq. lia.


    unfold k_of_N.
    rewrite H0.

    assert (Nat.eqb (k-1) 0 = false).
    apply PeanoNat.Nat.eqb_neq. lia.
    rewrite H3.

    rewrite <- filter_lists_by_length_map_comm.

    assert (S (k-1) = k). lia.
    rewrite H4.

    reflexivity.
Qed.

End SubLists.

Section filter_ext.

Lemma filter_split A (f : A -> bool) (l: list A):
  Permutation l (filter f l ++ filter (fun x => negb (f x)) l).
Proof.
  induction l.
  - intuition.
  - simpl. destruct (f a); simpl.
    * intuition.
    * apply Permutation_cons_app, IHl.
Qed.

End filter_ext.

Section Forall_map.

(*| This lemma generalizes :coq:`Forall_map` to forall. |*)

Lemma forall_map (A B: Type) (f : A -> B) (P: B -> Prop) (l: list A):
(forall x, In x (map f l) -> P x) <-> (forall x, In x l -> P (f x)).
Proof.
  induction l.
  - simpl. intuition.
  - split.
    + intros. apply H. destruct H0.
      * left. apply f_equal. intuition.
      * right. apply in_map. intuition.
    + cbn. intros. destruct H0.
      * generalize H0. subst. intuition.
      * intuition.
Qed.

End Forall_map.

Section option_type.

Variable T : Type.

Lemma None_not_Some: forall (x: option T) ,
  (exists t, x = Some t) <-> x <> None.
Proof.
  intros.
  split.
  destruct x.
  - discriminate.
  - intros. inversion H. contradict H0. discriminate.
  - intros. destruct x.
    + exists t. reflexivity.
    + contradiction H. reflexivity.
Qed.

End option_type.
