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
(*|

**************************************
Labelled Transitionsition System (LTS)
**************************************

In this chapter, we define Labelled Transition Systems (or LTS). This definition
follows the canonical definition of a *deterministic* LTS, see :math:`\cite{gorrieriLabeledTransitionSystems2017a}` for details. |*)

(*| .. coq:: none |*)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Section LTS_Definition.
(*| .. coq:: no-out |*)

(*|

===================
Definition of a LTS
===================

 A labeled transition system (or LTS) is a triple LTS = (S, A, Step) where

* S is the nonempty, countable set of states
* A is the countable set of labels (or actions);
* Step : S x A x S is the transition relation.

*Note*: we define :coq:`LTS_Step` as a function rather than a proposition. The :coq:`Step` function allows building a simulator, whereas the relation supports only proof.

|*)

  Definition LTS_Step (S : Type) (A : Type) := S -> A -> S.

  Record LTS_struct : Type := mkLTS_struct {
    States : Type;
    Actions : Type;
    Step : LTS_Step States Actions;
    Init : States;
  }.

(*| :coq:`step_lts` performs one step of the LTS. |*)

  Definition step_lts (A_LTS : LTS_struct)
                      (state: States A_LTS)
                      (action : Actions A_LTS) :=
    (Step A_LTS) state action.

(*| .. coq:: none |*)
Section LTS_Properties.
(*| .. coq:: no-out |*)

(*|

===================
Properties of a LTS
===================

We define :coq:`Transitions` as a predicate that returns
:coq:`True` iff :math:`s \xrightarrow{\text{a}} s'`.

|*)

Definition Transitions
  (L : LTS_struct) (s : States L) (a : Actions L) (s' : States L) :=
  (Step L) s a = s'.

(*| :coq:`Reachable` is a predicate that evaluates to True if a state is reachable from s. We use an inductive definition to defines this predicate with the following two case: either s is accessible from s, else if s1 is accessible from s and a transition from s1 to s2 exists, then s2 is also accessible from s.
|*)

Inductive Reachable (L : LTS_struct) (s : States L) :
  States L -> Prop :=
  | reachable_default : Reachable L s s
  | reachable_step :
      forall (s1 s2 : States L) (t : Actions L),
      Reachable L s s1 -> Transitions L s1 t s2
      -> Reachable L s s2.

(*| :coq:`Deadlock` returns True if s1 is a deadlock state, i.e. there is no transition from s1. |*)

Definition Deadlock (L : LTS_struct) (s1 : States L) : Prop :=
  forall (t : Actions L) (s2 : States L), ~ Transitions L s1 t s2.

(*| Definition of a :coq:`Bisimulation` relation. |*)

Definition Bisimulation (L : LTS_struct)
                        (R : relation (States L)) : Prop :=
  forall p q : States L, R p q ->
  (forall (a : Actions L) (p' : States L), Transitions L p a p' ->
    exists2 q' : States L, Transitions L q a q' & R p' q') /\
  (forall (a : Actions L) (q' : States L), Transitions L q a q' ->
    exists2 p' : States L, Transitions L p a p' & R p' q').

(*| Two States are bisimilar when a bisimulation exists. |*)

Inductive Bisimilar (L : LTS_struct) (p q : States L) : Prop :=
    bisimilar_exist :
      forall R : relation (States L),
      R p q -> Bisimulation L R -> Bisimilar L p q.

(*| .. coq:: none |*)
Section Results.

Variable L : LTS_struct.

Lemma Bisimilar_Refl : reflexive (States L) (Bisimilar L).
Proof.
  intros.

  (* To prove this lemma, we build a trivial bisimulation relation: the identity. *)
  exists (fun (p q : States L) => p = q). trivial.
  split; intros.

  (* From there, we exhibit a solution for each existential statement*)
  - exists p'; trivial. rewrite <- H; trivial.
  - exists q'; trivial. rewrite H; trivial.
Qed.

Lemma Bisimilar_Sym : symmetric (States L) (Bisimilar L).
Proof.
  (* introduce all variables *)
  unfold symmetric.
  intros ; elim H; intros.

  (* To prove this lemma, we propose the R' relation, which
    is the symetric of R and reduce all terms *)
  exists (fun p q : States L => R q p); trivial.
  red in |- *; intros.

  (* We can now combine H1 and H2 to conclude *)
  elim H1 with (1 := H2); auto.
Qed.

Lemma Bisimilar_Trans : transitive (States L) (Bisimilar L).
Proof.
  unfold transitive.

  (* introduce all variable. We turn Bisimilar predicates into Bisimulation *)
  intros p q r H1 H2. case H1. case H2. clear H1 H2. intros.

  (* the previous steps introduced relations R0 between p and q, and R between
     q and r. We use them to build a new relation that relates p and r*)
  exists (fun p r : States L => exists2 q : States L, R0 p q & R q r).
  - exists q; auto.
  - red in |- *; intros.

    (* from that point, the game is to break all quantifiers and exhibit
    solutions *)
    case H3; clear H3; intros.
    case H2 with (1 := H3); clear H2; intros.
    case H0 with (1 := H4); clear H0; intros.
    split; intros.
    * case H2 with (1 := H7); clear H2; intros.
      case H0 with (1 := H2); clear H0; intros.
      exists x1; trivial; exists x0; trivial.
    * case H6 with (1 := H7); clear H6; intros.
      case H5 with (1 := H6); clear H5; intros.
      exists x1; trivial; exists x0; trivial.
Qed.
(*| .. coq::  |*)

(*|
:coq:`Bisimilar` is an equivalence relation.
|*)

Instance Bisimilar_Equivalence : Equivalence (Bisimilar L) := {|
  Equivalence_Reflexive := Bisimilar_Refl;
  Equivalence_Symmetric := Bisimilar_Sym ;
  Equivalence_Transitive := Bisimilar_Trans ;
|}.

(*| .. coq:: none |*)
End Results.

End LTS_Properties.

End LTS_Definition.

(* Example *)

Section Example.

Inductive ab : Set := A | B.
Inductive ab_actions : Set := ReadA | ReadB | Fail.

Definition AB_Transitions (s1 : ab) (a: ab_actions) (s2 : ab) : bool :=
    match s1, a, s2 with
    | A, _, B => true
    | B, _, A => true
    | _, _, _ => false
    end.

Definition AB_Steps (s1 : ab) (a: ab_actions) :=
  match s1, a  with
  | A, _ => B
  | B, _ => A
  end.

Definition LTS_Test : LTS_struct := {|
  States := ab;
  Init := A;
  Actions := ab_actions;
  Step := AB_Steps;
|}.

Example f' := step_lts LTS_Test (Init LTS_Test) ReadA.
Lemma test : f' = B.
Proof.
  auto.
Qed.

Example LTS_Test_All_Reachable : forall s : ab, Reachable LTS_Test A s.
Proof.
  intros.
  induction s.
  - apply reachable_default.
  - apply reachable_step with (s1 := A) (t := ReadA).
    * apply reachable_default.
    * unfold Transitions; auto.
Qed.

End Example.
(*| .. coq:: |*)
