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

(*| .. coq:: none |*)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.

Require Import Oqarina.coq_utils.all.
Require Import Oqarina.core.all.
Require Import Oqarina.formalisms.FaultTrees.Merle_Algebra.

Require Import Top.tree.

Set Implicit Arguments.
(*| .. coq:: |*)

(*|

***********
Fault Trees
***********
Katoen

SOTERIA_PP https://ieeexplore.ieee.org/document/8769216

Target The Annual Reliability and Maintainability Symposium, track CfP for 2024, deadline approx. April

In this module, we provide a basic definition of fault trees as a collection of inductive types. |*)

(*| .. coq:: none |*)
Section Abstract_Fault_Tree.
(*| .. coq:: |*)

(*|
Abstract Fault Trees
====================

We define an fault tree as an AST over FT_Node, a type representing the various gates of a fault tree. Each gate  (AND, OR, ...) represents a combinatorial function of some basic event.

A basic event is defined as a generic type. Note: we may not need a dedicably equality for this type.

|*)

Variable basic_event : Type.

Hypothesis basic_event_eq_dec : forall x y : basic_event,
    { x = y } + { x <> y }.

Inductive FT_Node : Type :=
    | BASIC (b : basic_event)
    | OR
    | AND
    | PAND
    | SPARE
    | FDEP
    | K_OUT_OF_N (k : nat).

Lemma FT_Node_eq_dec : forall x y : FT_Node, { x = y } + { x <> y }.
Proof.
    repeat decide equality.
Qed.

Definition fault_tree := tree FT_Node.

(*| .. coq:: none |*)
Section Fault_Tree_Reduction.
(*| .. coq:: |*)

(*|
Reduction of Fault Trees
========================

A Fault Tree can generally be reduced through specifc tree transformations. In this section, we first define those lemmas as propositions, then provide an implementation of those reduction rules and show they are correctly implemented.

Note: at this stage, we only reduce the root of a fault tree.  We must also consider more reduction rules, see for instance those in Merle_Algebra
|*)

Inductive red : relation (fault_tree) :=
    | red_AND_1: forall (a: fault_tree),
        red (in_tree AND [a]) (a)

    | red_AND_concatenate: forall a l,
        red (in_tree AND [a; in_tree AND l]) (in_tree AND (a :: l))

    | red_OR_concatenate: forall a l,
        red (in_tree OR [a; in_tree OR l]) (in_tree OR (a :: l))
.

Definition Rewrite_Fault_Tree (F : fault_tree)
    : fault_tree
    :=
match F with

    (* red_AND_concatenate *)
    | in_tree AND [a; in_tree AND l] =>
        in_tree AND (a :: l)

    (* red_OR_concatenate *)
    | in_tree OR [a; in_tree OR l] =>
        in_tree OR (a :: l)

    (* red_AND_1 *)
    | in_tree AND (h :: []) => h

    (* tauto *)
    | _ => F
end.

(*| First, we demonstrate that :coq:`Rewrite_Fault_Tree` is sound, that is for all pair (f, f') of fault trees, if f' is a reduction of  f, then it can be computed by executing :coq:`Rewrite_Fault_Tree`. |*)

Lemma Rewrite_Fault_Tree_Sound : forall (f f': fault_tree),
    red f f' -> Rewrite_Fault_Tree f = f'.
Proof.
    intros.
    inversion H ; simpl ; auto.
Qed.

(*| Then the opposite lemma. |*)

Lemma Rewrite_Fault_Tree_Complete' : forall (f : fault_tree),
    clos_refl_trans _ red f (Rewrite_Fault_Tree f).
Proof.
    intros.
    induction f.
    case a.

    (* BASIC *)
    - intros. simpl. apply rt_refl.

    (* OR *)
    - simpl. case ll.
        * apply rt_refl.
        * intros. case l.
            + apply rt_refl.
            + intros. case l0.
                ** destruct t0, f ; try apply rt_refl.
                    apply rt_step, red_OR_concatenate.
                ** intros. destruct t0. destruct f ; apply rt_refl.

    (* AND *)
    - simpl. case ll.
        * apply rt_refl.
        * intros. case l.
            + apply rt_step, red_AND_1.
            + intros. destruct t0, f ; try apply rt_refl. case l0.
                ** apply rt_step, red_AND_concatenate.
                ** intros. destruct t0. destruct f ; apply rt_refl.

    (* PAND *)
    - simpl. apply rt_refl.

    (* SPARE *)
    - simpl. apply rt_refl.

    (* FDEP *)
    - simpl. apply rt_refl.

    (* K_OUT_OF_N *)
    - intros. simpl. apply rt_refl.
Qed.

Lemma Rewrite_Fault_Tree_Complete : forall (f f': fault_tree),
    Rewrite_Fault_Tree f = f' -> clos_refl_trans _  red f f'.
Proof.
    intros. subst. apply Rewrite_Fault_Tree_Complete'.
Qed.

(*| Finally, we define recursrive functions that apply the reduction to all nodes. |*)

Definition Rewrite_Fault_Tree' : fault_tree -> fault_tree.
Proof.
    induction 1 as [ x y IH ] using tree_recursion.
    apply (Rewrite_Fault_Tree (in_tree x IH)).
Defined.

Fixpoint Rewrite_Fault_Tree'' (f : fault_tree) :=
    let 'in_tree x ll := f in
    Rewrite_Fault_Tree (in_tree x (map Rewrite_Fault_Tree'' ll)).

(*| .. coq:: none |*)
End Fault_Tree_Reduction.

Section Static_Fault_Tree.
(*| .. coq:: |*)
(*|

Static Fault Trees
==================

A static fault tree, based on Dugan definition, has only three gates: OR, AND, and K-out-of-N. By definition, a fault tree is valid iff. each node of the tree is valid. |*)

Definition valid_static_fault_tree_node
    (n : FT_Node) (l : list fault_tree)
    : Prop
:=
    match n with
        | BASIC _ => l = []
        | K_OUT_OF_N k => k < (List.length l)
        | FDEP => False
        | SPARE => False
        | PAND => False
        | AND | OR => True
    end.

Lemma valid_static_fault_tree_node_dec:
    forall  (n : FT_Node) (l : list fault_tree),
    { valid_static_fault_tree_node n l } +
        { ~ valid_static_fault_tree_node n l }.
Proof.
    prove_dec.
    apply list_eq_dec. apply tree_eq_dec. apply FT_Node_eq_dec.
    apply Compare_dec.le_dec.
Qed.

Definition valid_static_fault_tree (sft : fault_tree) :=
    tree_fall valid_static_fault_tree_node sft.

Lemma valid_static_fault_tree_dec:
    forall (sft : fault_tree),
    { valid_static_fault_tree sft } +
        { ~ valid_static_fault_tree sft }.
Proof.
    apply tree_fall_dec.
    apply valid_static_fault_tree_node_dec.
Qed.

Fixpoint valid_static_fault_tree' (f : fault_tree) : Prop :=
    let 'in_tree x ll := f in
    valid_static_fault_tree_node x ll /\
        All valid_static_fault_tree' ll.

Lemma valid_static_fault_tree'_dec:
    forall (sft : fault_tree),
    { valid_static_fault_tree' sft } +
        { ~ valid_static_fault_tree' sft }.
Proof.
    induction sft.
    simpl.
    apply dec_sumbool_and.
    - apply valid_static_fault_tree_node_dec.
    - induction ll.
        * simpl ; auto.
        * simpl. apply dec_sumbool_and.
            + apply X ; simpl ; auto.
            + apply IHll. intuition.
Qed.

(*| .. coq:: none |*)
End Static_Fault_Tree.

Section Dynamic_Fault_Tree.
(*| .. coq:: |*)
(*|

Dynamic Fault Trees
===================

 |*)

Definition valid_dynamic_fault_tree_node
    (n : FT_Node) (l : list fault_tree)
    : Prop
:=
    match n with
        | BASIC _ => l = []
        | K_OUT_OF_N k => k < (List.length l)
        | FDEP => True
        | SPARE => (List.length l) = 3
        | PAND => True
        | AND | OR => True
    end.

Lemma valid_dynamic_fault_tree_node_dec:
    forall  (n : FT_Node) (l : list fault_tree),
    { valid_static_fault_tree_node n l } +
        { ~ valid_static_fault_tree_node n l }.
Proof.
    prove_dec.
    apply list_eq_dec. apply tree_eq_dec. apply FT_Node_eq_dec.
    apply Compare_dec.le_dec.
Qed.

Definition valid_dynamic_fault_tree (sft : fault_tree) :=
    tree_fall valid_static_fault_tree_node sft.

Lemma valid_dynamic_fault_tree_dec:
    forall (sft : fault_tree),
    { valid_static_fault_tree sft } +
        { ~ valid_static_fault_tree sft }.
Proof.
    apply tree_fall_dec.
    apply valid_static_fault_tree_node_dec.
Qed.

(*| .. coq:: none |*)
End Dynamic_Fault_Tree.

Section Fault_Tree_Evaluation.
(*| .. coq:: |*)

(*|

Evaluation of a fault tree
==========================

In this section, we define a generic function :coq:`Compute_Fault_Node` that evaluates the value of a fault node. It is parameterized by the typeclass :coq:`Basic_Event_Operators` that provides basic operator for a given type class.

|*)

Class Basic_Event_Operators (A : Type) :=
{
 (*   A_eq_dec : forall (x y : A), {x = y} + {x ≠ y} ; *)
    T  : A ;
    F : A ;
    b_AND : A -> A -> A ;
    b_OR : A -> A -> A ;

    b_ANDl : list A -> A ;
    b_ANDl_singleton : forall (a: A), b_ANDl [a] = a ;

    b_ANDl_concatenate : forall (a: A) (l : list A),
        b_ANDl [a; b_ANDl l] = b_ANDl (a :: l) ;

    b_ORl : list A -> A ;

    b_ORl_concatenate : forall (a: A) (l : list A),
        b_ORl [a; b_ORl l] = b_ORl (a :: l) ;

    b_PANDl : list A -> option A ;

}.

Context `{ ba : Basic_Event_Operators basic_event }.

Definition Compute_Fault_Node
    (n : FT_Node)
    (l : list (option basic_event))
    : option basic_event
:=
    if has_none l then None
    else
    let l' := clean_options l in
    match n with
        | BASIC b => Some b
        | OR => Some (b_ORl l')
        | AND => Some (b_ANDl l')
        | K_OUT_OF_N k => None
        (*    if Nat.leb k (count_occ A_eq_dec l T) then T else F*)
        | FDEP => None
        | PAND => b_PANDl l'
        | SPARE => None
    end.

Definition Compute_Fault_Tree : fault_tree -> option basic_event.
Proof.
    induction 1 as [ x y IH ] using tree_recursion.
    apply (Compute_Fault_Node x IH).
Defined.

Fixpoint Compute_Fault_Tree'' (f : fault_tree ) : option basic_event :=
     let 'in_tree x ll := f in
        Compute_Fault_Node x (map Compute_Fault_Tree'' ll).

Fact Compute_Fault_Tree_fix x ll :
    Compute_Fault_Tree (in_tree x ll) =
    Compute_Fault_Node x (map Compute_Fault_Tree ll).
Proof.
    apply tree_recursion_fix.
Qed.

Fact Compute_Fault_Tree''_fix x ll :
    Compute_Fault_Tree'' (in_tree x ll) =
    Compute_Fault_Node x (map Compute_Fault_Tree'' ll).
Proof.
    auto.
Qed.

Lemma Compute_Fault_Tree_OK:
    forall s, Compute_Fault_Tree s = Compute_Fault_Tree'' s.
Proof.
    intros.
    induction s.
    rewrite Compute_Fault_Tree_fix.
    rewrite Compute_Fault_Tree''_fix.

    apply map_ext_in in H.
    apply f_equal ; auto.
Qed.

Lemma Compute_Fault_Tree_sound : forall s s',
    red s s' -> Compute_Fault_Tree'' s = Compute_Fault_Tree'' s'.
Proof.
    intros.
    inversion H.
    subst.
    - simpl ; destruct (Compute_Fault_Tree'' s') ; unfold Compute_Fault_Node.
      * assert (has_none [Some b] = false).
        + compute ; reflexivity.
        + simpl ; rewrite b_ANDl_singleton ; reflexivity.
      * compute ; reflexivity.

    - simpl. destruct (Compute_Fault_Tree'' a).
      * unfold Compute_Fault_Node. repeat rewrite has_none_Some.
      destruct (has_none (map Compute_Fault_Tree'' l)).
        + compute ; reflexivity.
        + simpl. rewrite b_ANDl_concatenate ; reflexivity.
      * unfold Compute_Fault_Node. compute ; reflexivity.

    - simpl. destruct (Compute_Fault_Tree'' a).
        * unfold Compute_Fault_Node. repeat rewrite has_none_Some.
        destruct (has_none (map Compute_Fault_Tree'' l)).
        + compute ; reflexivity.
        + simpl. rewrite b_ORl_concatenate ; reflexivity.
        * unfold Compute_Fault_Node. compute ; reflexivity.
Qed.

(*| .. coq:: none |*)
End Fault_Tree_Evaluation.

End Abstract_Fault_Tree.

Ltac prove_valid_static_fault_tree :=
    repeat match goal with
    | [ |- forall x : ?T, _ ] => intros t H ; destruct H ; subst
    | [ |- valid_static_fault_tree _ ] => unfold valid_static_fault_tree
    | [ |- tree_fall _ _ ] => apply tree_fall_fix
    | [ |-  _ /\ _ ] => split
    | [ |- valid_static_fault_tree_node  _ _ ] => compute; auto
    | [ H : In _ _ |- _ ] => destruct H ; subst
end.

Section Fault_Tree_Bool.
(*| .. coq:: |*)

(*|

Boolean fault tree
==================

Stupid instantiation of the previous abstract fault tree. Basic events are simple booleans.

|*)

#[global]
Instance bool_Basic_Event_Operators : Basic_Event_Operators bool :=
{
   (* A_eq_dec := bool_dec ;*)
    T := true ;
    F := false ;

    b_AND := andb ;
    b_ANDl_singleton := andbl_singleton ;

    b_ANDl := andbl ;
    b_ANDl_concatenate := andbl_concatenate ;

    b_OR := orb ;

    b_ORl := orbl ;
    b_ORl_concatenate := orbl_concatenate ;

    (* For boolean fault tree, the following gates are not defined ‘*)

    b_PANDl := (fun x => None) ;
}.

Definition BFT := fault_tree bool.

(*| .. coq:: none |*)
End Fault_Tree_Bool.

Section Fault_Tree_Bool_Examples.
(*| .. coq::  |*)

(*| From these definitions, one can directly built a fault tree, check it is correct, and evaluate it. |*)

Example Basic_BFT : BFT :=
    in_tree (AND bool)
    [ in_tree (BASIC true) [] ;
      in_tree (BASIC false) []].

Fact Basic_BFT_OK : valid_static_fault_tree Basic_BFT.
Proof.
    prove_valid_static_fault_tree.
Qed.

Lemma Compute_Fault_Tree_Basic_BFT_OK:
    Compute_Fault_Tree'' Basic_BFT = Some false.
Proof.
    trivial.
Qed.

(*| .. coq:: none |*)
End Fault_Tree_Bool_Examples.

Section DFT.
(*| .. coq:: |*)

(*|

Dynamic fault tree
==================

In this section, we build Dynamic Fault Tree, using Merle's Algebra operators for the fault tree evaluation :cite:t:`merle:tel-00502012`.

|*)

Variable basic_event : Type.

Definition d' := Merle_Algebra.d basic_event.

#[global]
Instance Merle_Basic_Event_Operators : Basic_Event_Operators d' :=
{
    T := d_0 basic_event ;
    F := d_inf basic_event ;

    b_AND := D_AND basic_event ;
    b_ANDl_singleton := Rule_4 basic_event ;

    b_ANDl := n_AND basic_event ;
    b_ANDl_concatenate := Rule_8' basic_event ;

    b_OR := D_OR basic_event ;

    b_ORl := n_OR basic_event ;
    b_ORl_concatenate := Rule_9' basic_event ;

    b_PANDl := (fun x => Some (n_PAND basic_event x));
}.

Definition DFT := fault_tree d'.

(*| From these definitions, one can directly built a fault tree, check it is correct, and evaluate it. |*)

Example Basic_DFT : DFT :=
    in_tree (PAND d')
    [ in_tree (BASIC (d_0 basic_event)) [] ;
      in_tree (BASIC (d_0 basic_event)) []].

      (*
Fact Basic_DFT_OK : ~ valid_static_fault_tree Basic_DFT.
Proof.

    prove_valid_static_fault_tree.
Qed.
*)

Lemma Compute_Fault_Tree_Basic_DFT_OK:
    Compute_Fault_Tree'' Basic_DFT =
        Some (fun d : basic_event => Ndist.ni 0).
Proof.
    trivial.
Qed.

(*| .. coq:: none |*)
End DFT.
(*| .. coq:: |*)

