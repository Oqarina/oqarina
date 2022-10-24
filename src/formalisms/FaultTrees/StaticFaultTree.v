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
Require Import Floats. Open Scope float_scope.

(* Oqarina Library*)
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.core.all.
Require Import Oqarina.formalisms.FaultTrees.AbstractFaultTree.
Require Import Oqarina.formalisms.Expressions.all.

Set Implicit Arguments.
Set Strict Implicit.
(*| .. coq:: |*)

(*|

******************
Static Fault Trees
******************


A static fault tree, based on Dugan definition, has only three gates: OR, AND, and K-out-of-N. Note that K-out-of-N are rewritten as a collection of OR and AND gates (see :coq:`Rewrite_Fault_Tree_r` in  :doc:`formalisms__FaultTrees_AbstractFaultTree.v` ). We do not consider K-out-of_N gates in the following.

We provide definitions for a valid fault tree (section :ref:`Definitions`). Them, we provide implementations of boolean-valued fault trees (section :ref:`Boolean-valued fault trees`) and float-value fault trees (:ref:`Floating-point valued fault trees`).

|*)

(*| .. coq:: none |*)
Section Static_Fault_Tree.
(*| .. coq:: |*)

(*|

Definitions
===========

|*)

Variable basic_event : Set.
Hypothesis basic_event_eq_dec : forall x y : basic_event,
    { x = y } + { x <> y }.

Definition valid_static_fault_tree_node
    (n : FT_Node basic_event) (l : list (fault_tree basic_event))
    : Prop
:=
    match n with
        | INVALID _ => False
        | BASIC _ => l = []
        | K_OUT_OF_N _ k => False (* rewritten *)
        | FDEP _ => False
        | SPARE _ => False
        | PAND _ => False
        | AND _| OR _=> True
    end.

Lemma valid_static_fault_tree_node_dec:
    forall (n : FT_Node basic_event)
           (l : list (fault_tree basic_event)),
    { valid_static_fault_tree_node n l } +
        { ~ valid_static_fault_tree_node n l }.
Proof.
    prove_dec.
    apply List.list_eq_dec,tree_eq_dec, FT_Node_eq_dec.
    apply basic_event_eq_dec.
Qed.

Definition valid_static_fault_tree
    (sft : fault_tree basic_event)
:=
    tree_fall valid_static_fault_tree_node sft.

Lemma valid_static_fault_tree_dec:
    forall (sft : fault_tree basic_event),
    { valid_static_fault_tree sft } +
        { ~ valid_static_fault_tree sft }.
Proof.
    apply tree_fall_dec.
    apply valid_static_fault_tree_node_dec.
Qed.

Fixpoint valid_static_fault_tree'
    (f : fault_tree basic_event)
:=
    let 'in_tree x ll := f in
    valid_static_fault_tree_node x ll /\
        All valid_static_fault_tree' ll.

Lemma valid_static_fault_tree'_dec:
    forall (sft : fault_tree basic_event),
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

Lemma valid_static_fault_tree'_children:
    forall a ll,
        valid_static_fault_tree' (in_tree a ll) ->
            forall x, In x ll ->
            valid_static_fault_tree' x.
Proof.
    intros.

    unfold valid_static_fault_tree' in H.
    destruct H.
    rewrite <- All_In in H1.
    fold valid_static_fault_tree' in H1.
    auto.
Qed.

Lemma valid_static_fault_tree'_car: forall a a0 ll,
    valid_static_fault_tree' (in_tree a (a0 ::ll)) ->
    valid_static_fault_tree' a0.
Proof.
    intros.
    apply valid_static_fault_tree'_children
        with (a:=a) (ll:=a0::ll).
    apply H. apply in_eq.
Qed.

Lemma valid_static_fault_tree'_cons: forall a a0 ll,
    valid_static_fault_tree' (in_tree a (a0 ::ll)) ->
    valid_static_fault_tree' (in_tree a ll).
Proof.
    intros.
    unfold valid_static_fault_tree' in *.
    simpl in H.
    intuition.

    generalize H0.
    unfold valid_static_fault_tree_node.
    case a ; intuition.
    apply eq_sym  in H1. contradict H1.  apply nil_cons.
Qed.

(*| .. coq:: none |*)
End Static_Fault_Tree.

Section k_out_of_n.
(*|
k-out-of-N gate
===============

We provide a definition of the k-out-of-N gate for the boolean case, along with two simplification results.

|*)

Definition k_out_of_n_bool (k : nat) (l : list bool)  :=
    if Nat.leb k (count_occ bool_dec l true)
    then true else false.

Lemma k_out_of_N_OR: forall (l : list bool),
    k_out_of_n_bool 1 l = orbl l.
Proof.
    intros.
    unfold k_out_of_n_bool.
    induction l.
    - intuition.
    - destruct a.
        * rewrite count_occ_cons_eq.
            + simpl ; rewrite orbl_true ; reflexivity.
            + intuition.
        * rewrite count_occ_cons_neq.
            + rewrite orbl_false. apply IHl.
            + intuition.
Qed.

Lemma k_out_of_N_AND: forall (l : list bool),
        k_out_of_n_bool (List.length l) l = andbl l.
Proof.
    unfold k_out_of_n_bool. simpl.
    induction l.
    - intuition.
    - destruct a.
        * rewrite count_occ_cons_eq.
            + rewrite andbl_true. rewrite length_S.
              assert (Nat.leb (S (List.length l)) (S (count_occ bool_dec l true)) = Nat.leb (List.length l) (count_occ bool_dec l true)). intuition.
              apply IHl.
            + intuition.
        * rewrite count_occ_cons_neq.
            + intros. rewrite length_S.
              assert (Nat.leb (S (Datatypes.length l)) (count_occ bool_dec l true) = false).
              rewrite PeanoNat.Nat.leb_gt.
              generalize count_occ_bound ; intuition. rewrite H. rewrite andbl_false ; reflexivity.
            + intuition.
Qed.

(*| .. coq:: none|*)
End k_out_of_n.

Section Fault_Tree_Bool.
(*| .. coq:: |*)

(*|

Boolean-valued fault trees
==========================

One basic way to use abstract fault trees is to instantiate basic events as booleans.

|*)

#[global]
Instance bool_Basic_Event_Operators : Basic_Event_Operators bool :=
{
    T := true ;
    F := false ;

    b_AND := andb ;
    b_ANDl := andbl ;

    b_OR := orb ;
    b_ORl := orbl ;

    (* For boolean fault tree, the following gates are not defined ‘*)

    b_PANDl := (fun x => None) ;
}.

#[global]
Instance bool_Basic_Event_Operators_Facts : Basic_Event_Operators_Facts bool_Basic_Event_Operators :=
{
    b_ANDl_singleton := andbl_singleton ;
    b_ANDl_concatenate := andbl_concatenate ;
    b_ORl_concatenate := orbl_concatenate ;
}.

Definition BFT := fault_tree bool.

(*| .. coq:: none |*)
End Fault_Tree_Bool.

Section Fault_Tree_Float.
(*| .. coq:: |*)

(*|

Floating-point valued fault trees
=================================

|*)

Definition f_AND (f1 f2: float) := f1 * f2.
Definition f_OR (f1 f2: float) := f1 + f2.

Definition f_ANDl (l : list float ):=
    fold_right (fun a b => (f_AND a b)) 1 l.

Definition f_ORl (l : list float ):=
    fold_right (fun a b => (f_OR a b)) 0 l.

#[global]
Instance float_Basic_Event_Operators : Basic_Event_Operators float :=
{
    T := 1 ;
    F := 0 ;

    b_AND := mul ;
    b_ANDl := f_ANDl ;

    b_OR := add ;
    b_ORl := f_ORl ;

    b_PANDl := (fun x => None) ;
}.

Definition FFT := fault_tree float.

(*| .. coq:: none |*)
End Fault_Tree_Float.


(*|

Mapping static fault trees to Boolean Expressions
=================================================

|*)

(*| .. coq:: none |*)
Section Fault_Tree_to_Bool_Expr.
(*| .. coq:: |*)

Variable basic_event : Set.
Variable basic_event_beq: basic_event → basic_event → bool.

Fixpoint Map_to_OR
    (l : list (PropF basic_event))
    : PropF basic_event
:=
    match l with
        | nil => Bot basic_event
        | h :: t => Disj h (Map_to_OR t)
    end.

Fixpoint Map_to_AND
    (l : list (PropF basic_event))
    : PropF basic_event
:=
    match l with
        | nil => Top basic_event
        | h :: t => Conj h (Map_to_AND t)
    end.

Definition Map_Fault_Node_to_BoolExpr
    (n : FT_Node basic_event)
    (l : list (PropF basic_event))
    : PropF basic_event
:=
    match n with
        | BASIC b => Var b
        | OR _     => Map_to_OR l
        | AND _    => Map_to_AND l
        | _        => Bot basic_event
end.

Fixpoint Map_Fault_Tree_to_BoolExpr'
    (f : fault_tree basic_event)
    : PropF basic_event
:=
    let 'in_tree x ll := f in
        Map_Fault_Node_to_BoolExpr x (map Map_Fault_Tree_to_BoolExpr' ll).

Definition Map_Fault_Tree_to_BoolExpr
    (f : fault_tree basic_event)
    : PropF basic_event
:=
    Map_Fault_Tree_to_BoolExpr' (Rewrite_Fault_Tree'' f).

Lemma Map_Fault_Tree_to_BoolExpr'_sound:
    forall (f: fault_tree basic_event) (v : basic_event -> bool),
        valid_static_fault_tree' f ->
            Compute_Fault_Tree_2 f v =
            Eval_PropF v (Map_Fault_Tree_to_BoolExpr' f).
Proof.
    intros f v.
    induction f.

    (* We do a case analysis on the value of the gate 'a'
      and expedite trivial cases via intuition. *)
    case a ; intuition ; induction ll.

    (* OR *)
    - intuition.

    - assert (forall x, In x ll -> valid_static_fault_tree' x ->
                Compute_Fault_Tree_2 x v =
                Eval_PropF v (Map_Fault_Tree_to_BoolExpr' x)).
     intuition. (* Consequence of H0 *)

     assert (Compute_Fault_Tree_2 (in_tree (OR basic_event) ll) v =
        Eval_PropF v
            (Map_to_OR
            (map (Map_Fault_Tree_to_BoolExpr') ll))).
     apply IHll. apply H1.

     apply valid_static_fault_tree'_cons in H0. apply H0.

     simpl. rewrite orbl_cons.

     assert (Compute_Fault_Tree_2 a0 v =
                Eval_PropF v (Map_Fault_Tree_to_BoolExpr' a0)).
     apply H. apply in_eq.

     apply valid_static_fault_tree'_car in H0. apply H0.

     rewrite H3. rewrite <- H2.
     intuition.

    (* AND *)
    - intuition.

    - assert (forall x, In x ll -> valid_static_fault_tree' x ->
                Compute_Fault_Tree_2 x v =
                Eval_PropF v (Map_Fault_Tree_to_BoolExpr' x)).
      intuition. (* Consequence of H0 *)

     assert (Compute_Fault_Tree_2 (in_tree (AND basic_event) ll) v =
        Eval_PropF v
            (Map_to_AND
            (map (Map_Fault_Tree_to_BoolExpr') ll))).
     apply IHll. apply H1.
     apply valid_static_fault_tree'_cons in H0. apply H0.

     simpl. rewrite andbl_cons.

     assert (Compute_Fault_Tree_2 a0 v =
                Eval_PropF v (Map_Fault_Tree_to_BoolExpr' a0)).
     apply H. apply in_eq.

     apply valid_static_fault_tree'_car in H0. apply H0.

     rewrite H3. rewrite <- H2.
     intuition.

     (* K_OUT_OF_N *)
     - simpl in H0. intuition.
     - simpl in H0. intuition.
Qed.

Fixpoint Map_BoolExpr_to_Fault_Tree
    (b : PropF basic_event)
    : fault_tree basic_event
:=
    match b with
        | Var b => in_tree (BASIC b) []

        | Conj b1 b2 => in_tree (AND _)
            [ Map_BoolExpr_to_Fault_Tree b1 ;
              Map_BoolExpr_to_Fault_Tree b2 ]

        | Disj b1 b2 => in_tree (OR _)
            [ Map_BoolExpr_to_Fault_Tree b1 ;
              Map_BoolExpr_to_Fault_Tree b2 ]

        | _ => invalid_tree basic_event
    end.

    (*
Lemma Map_BoolExpr_to_Fault_Tree_sound:
    forall (p: PropF basic_event) (v : basic_event -> bool),
        Compute_Fault_Tree_2 (Map_BoolExpr_to_Fault_Tree p) v =
        Eval_PropF v p.
Proof.
    intros p v.
    induction p.

    - simpl. intuition.
    - simpl. intuition.
    - simpl. rewrite IHp1, IHp2. intuition.
    - simpl. rewrite IHp1, IHp2. intuition.
    - simpl.
*)


(*| .. coq:: none |*)
End Fault_Tree_to_Bool_Expr.
(*| .. coq:: |*)

(*|

Minimal cutset of a static fault tree
=====================================
|*)

(*| .. coq:: none |*)
Section Minimal_cutset.
(*| .. coq:: |*)

Variable basic_event : Set.
Variable basic_event_beq: basic_event → basic_event → bool.

Definition Map_Fault_Tree_to_Cutset
    (f : fault_tree basic_event)
    : PropF basic_event
:=
    Rewrite_PropF_r
        (PropF_to_cutset basic_event_beq (Map_Fault_Tree_to_BoolExpr f)).

(*| .. coq:: none |*)
End  Minimal_cutset.
(*| .. coq:: |*)
