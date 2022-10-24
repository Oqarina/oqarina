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
(* Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.

(* Oqarina Library*)
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.core.all.
Require Import Oqarina.formalisms.Expressions.all.

Require Export Top.tree.

Set Implicit Arguments.
Set Strict Implicit.
(*| .. coq:: |*)

(*|

********************
Abstract Fault Trees
********************

In this module, we provide a general definition of fault trees as an inductive type (section :ref:`Definition`).

Then, we introduce reduction functions that rewrite fault trees using simpler terms (section :ref:`Reduction of Fault Trees`). We first define reduction rules, then a function that implements these transformations. We show the transformation is sound.

In section :ref:`Evaluation of a fault tree`, we define a generic evaluation function for fault trees as a typeclass. This function can be specialized for various types (e.g. boolean, floats, ...).

Finally, we introduce functions to compute the minimum cutset of a fault tree (section :ref:`Minimum cut-set of a fault tree`).

|*)

(*| .. coq:: none |*)
Section Abstract_Fault_Tree.
(*| .. coq:: |*)

(*|
Definition
==========

We define a fault tree as an AST over FT_Node, a type representing the various gates of a fault tree. Each gate  (AND, OR, ...) represents a combinatorial function of some basic events.

A basic event is defined as a generic type, equipped with a decidable equality and a boolean equality.

|*)

Variable basic_event : Set.

Hypothesis basic_event_eq_dec : forall x y : basic_event,
    { x = y } + { x <> y }.

Variable basic_event_beq: basic_event → basic_event → bool.
Hypothesis basic_event_reflect: forall x y,
    reflect (x = y) (basic_event_beq x y).

Inductive FT_Node : Type :=
    | INVALID
    | BASIC (b : basic_event)
    | OR
    | AND
    | PAND
    | SPARE
    | FDEP
    | K_OUT_OF_N (k : nat).

Lemma FT_Node_eq_dec : forall x y : FT_Node,
    { x = y } + { x <> y }.
Proof.
    repeat decide equality.
Qed.

Definition fault_tree := tree FT_Node.

Definition invalid_tree := in_tree INVALID [].

(*| :coq:`Get_Root_FT_Node` returns the FT_Node of the root of a fault tree. |*)

Definition Get_Root_FT_Node (f : fault_tree) :=
    match f with
    | in_tree n _ => n
    end.

(*| .. coq:: none |*)
Section Fault_Tree_Reduction.
(*| .. coq:: |*)

(*|
Reduction of Fault Trees
========================

A Fault Tree can generally be reduced through specifc tree transformations. In this section, we first define those lemmas as propositions (in :coq:`red`), then provide an implementation of those reduction rules (:coq:`Rewrite_Fault_Tree` and :coq:`Rewrite_Fault_Tree_r`)  and show they are correctly implemented.

|*)

Inductive red : relation (fault_tree) :=
    | red_AND_1: forall (a: fault_tree),
        red (in_tree AND [a]) (a)

    | red_AND_concatenate: forall a l,
        red (in_tree AND [a; in_tree AND l])
            (in_tree AND (a :: l))

    | red_OR_concatenate: forall a l,
        red (in_tree OR [a; in_tree OR l])
            (in_tree OR (a :: l))

    | red_K_OUT_OF_N: forall k l,
        red (in_tree (K_OUT_OF_N k) l)
        (in_tree OR (map (fun x => in_tree AND x)
                        (k_of_N k l))).

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

    (* red_K_OUT_OF_N *)
    | in_tree (K_OUT_OF_N k) l =>
        in_tree OR (map (fun x => in_tree AND x) (k_of_N k l))

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

Lemma Rewrite_Fault_Tree_Complete' :
    forall (f : fault_tree),
        clos_refl_trans _ red f (Rewrite_Fault_Tree f).
Proof.
    intros.
    induction f.
    case a.

    (* INVALID *)
    - intros. simpl. apply rt_refl.

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
                ** intros. destruct t0.
                   destruct f ; apply rt_refl.

    (* AND *)
    - simpl. case ll.
        * apply rt_refl.
        * intros. case l.
            + apply rt_step, red_AND_1.
            + intros. destruct t0, f ; try apply rt_refl.
              case l0.
                ** apply rt_step, red_AND_concatenate.
                ** intros. destruct t0. destruct f ; apply rt_refl.

    (* PAND *)
    - simpl. apply rt_refl.

    (* SPARE *)
    - simpl. apply rt_refl.

    (* FDEP *)
    - simpl. apply rt_refl.

    (* K_OUT_OF_N *)
    - intros. simpl. apply rt_step, red_K_OUT_OF_N.
Qed.

Lemma Rewrite_Fault_Tree_Complete : forall (f f': fault_tree),
    Rewrite_Fault_Tree f = f' ->
        clos_refl_trans _  red f f'.
Proof.
    intros. subst. apply Rewrite_Fault_Tree_Complete'.
Qed.

(*| Finally, we define recursive functions that apply the reduction to all nodes. |*)

Definition Rewrite_Fault_Tree' : fault_tree -> fault_tree.
Proof.
    induction 1 as [ x y IH ] using tree_recursion.
    apply (Rewrite_Fault_Tree (in_tree x IH)).
Defined.

Fixpoint Rewrite_Fault_Tree'' (f : fault_tree) :=
    let 'in_tree x ll := f in
    Rewrite_Fault_Tree
        (in_tree x (map Rewrite_Fault_Tree'' ll)).

Lemma Rewrite_Fault_Tree''_fix: forall x ll,
    Rewrite_Fault_Tree'' (in_tree x ll) =
        Rewrite_Fault_Tree
            (in_tree x (map Rewrite_Fault_Tree'' ll)).
Proof. trivial. Qed.

(*| A direct result of :coq:`Rewrite_Fault_Tree'` is that the K_OUT_OF_N gate has been suppressed. |*)

Lemma Rewrite_Fault_Tree'_postcondition:
    forall (f : fault_tree) k,
        Get_Root_FT_Node (Rewrite_Fault_Tree'' f)
            <> K_OUT_OF_N k.
Proof.
    intros.
    induction f.
    case a ;simpl ; try discriminate.

    (* OR gates *)
    - destruct ll.
        + simpl. discriminate.
        + simpl. destruct ll.
            * simpl. discriminate.
            * simpl.
              destruct (Rewrite_Fault_Tree'' t0).
              destruct f ; simpl ; try discriminate.
              destruct (map Rewrite_Fault_Tree'' ll) ;
                simpl ; discriminate.

    (** AND gates *)
    - destruct ll.
        + simpl. discriminate.
        + simpl.
          destruct (map Rewrite_Fault_Tree'' (ll)).

          assert (In t (t::ll)). apply in_eq.
          apply H, H0.

          destruct t0.
          destruct f ; simpl ; try discriminate.
          destruct l ; simpl ; discriminate.

Qed.

(*| .. coq:: none |*)
End Fault_Tree_Reduction.

Section Fault_Tree_Evaluation.
(*| .. coq:: |*)

(*|

Evaluation of a fault tree
==========================

In this section, we define a generic function :coq:`Compute_Fault_Node` that evaluates the value of a fault node. It is parameterized by the typeclass :coq:`Basic_Event_Operators` that provides basic operators for a given type and :coq:`Basic_Event_Operators_Facts` that provides associated lemmas.

We latter provide instances for booleans, floats, etc.

|*)

(*| .. coq:: none |*)
Section FT_Operators.
(*| .. coq:: |*)

Class Basic_Event_Operators (A : Type):=
{
    T : A ;
    F : A ;

    b_AND : A -> A -> A ;
    b_OR : A -> A -> A ;

    b_ANDl : list A -> A ;

    b_ORl : list A -> A ;

    b_PANDl : list A -> option A ;

    b_k_out_of_N (k : nat) (l : list A) :=
        b_ORl (map (fun x => b_ANDl x) (k_of_N k l)) ;
}.

Class Basic_Event_Operators_Facts `( ba : Basic_Event_Operators ) :=
{
    b_ANDl_singleton : forall (a: A), b_ANDl [a] = a ;

    b_ANDl_concatenate : forall (a: A) (l : list A),
        b_ANDl [a; b_ANDl l] = b_ANDl (a :: l) ;

    b_ORl_concatenate : forall (a: A) (l : list A),
        b_ORl [a; b_ORl l] = b_ORl (a :: l) ;

}.

(*| .. coq:: none |*)
End FT_Operators.
(*| .. coq:: |*)

(*| We define :coq:`Compute_Fault_Node` as a generic function that relies on instance of :coq:`Basic_Event_Operators` and :coq:`Basic_Event_Operators_Facts`.  |*)

Variable basic_event_value : Type.

Context `{ ba : Basic_Event_Operators basic_event_value }
`{ baf : Basic_Event_Operators_Facts  basic_event_value }.

Definition Compute_Fault_Node
    (n : FT_Node)
    v
    (l : list (option basic_event_value))
    : option basic_event_value
:=
    if has_none l then None
    else
    let l' := clean_options l in
    match n with
        | INVALID => None
        | BASIC b => Some(v b)
        | OR => Some (b_ORl l')
        | AND => Some (b_ANDl l')
        | K_OUT_OF_N k => Some (b_k_out_of_N k l')
        | FDEP => None
        | PAND => b_PANDl l'
        | SPARE => None
    end.

Definition Compute_Fault_Node_2
    (n : FT_Node)
    v
    (l : list basic_event_value)
    : basic_event_value
:=
    match n with
        | INVALID => F
        | BASIC b => v b
        | OR => b_ORl l
        | AND => b_ANDl l
        | K_OUT_OF_N k => b_k_out_of_N k l
        | FDEP => F
        | PAND => F (* XXX *)
        | SPARE => F
    end.

Fixpoint Compute_Fault_Tree''
    (f : fault_tree ) v
    : option basic_event_value
:=
     let 'in_tree x ll := f in
        Compute_Fault_Node x v
            (map (fun x => Compute_Fault_Tree'' x v) ll).

Fixpoint Compute_Fault_Tree_2
    (f : fault_tree ) v
    : basic_event_value
:=
    let 'in_tree x ll := f in
        Compute_Fault_Node_2 x v
            (map (fun x => Compute_Fault_Tree_2 x v) ll).

Lemma Compute_Fault_Tree_2_fix: forall x ll v,
    Compute_Fault_Tree_2 (in_tree x ll) v =
        Compute_Fault_Node_2 x v
            (map (fun x => Compute_Fault_Tree_2 x v) ll).
Proof. trivial. Qed.

(*| .. coq:: none |*)
End Fault_Tree_Evaluation.

End Abstract_Fault_Tree.
