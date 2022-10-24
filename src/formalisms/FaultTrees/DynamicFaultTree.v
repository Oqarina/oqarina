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
Require Import Oqarina.formalisms.FaultTrees.Merle_Algebra.
Require Import Oqarina.formalisms.Expressions.all.

Set Implicit Arguments.
Set Strict Implicit.
(*| .. coq:: |*)

(*|

*******************
Dynamic Fault Trees
*******************

|*)

Section Dynamic_Fault_Tree.
(*| .. coq:: |*)

Variable basic_event : Set.
Hypothesis basic_event_eq_dec : forall x y : basic_event,
    { x = y } + { x <> y }.

Definition valid_dynamic_fault_tree_node
    (n : FT_Node basic_event) (l : list (fault_tree basic_event))
    : Prop
:=
    match n with
        | INVALID _ => False
        | BASIC _ => l = []
        | K_OUT_OF_N _ k => k <= (List.length l)
        | FDEP _ => True
        | SPARE _ => (List.length l) = 3%nat
        | PAND _ => True
        | AND _ | OR _ => True
    end.

Lemma valid_dynamic_fault_tree_node_dec:
    forall (n : FT_Node basic_event) (l : list (fault_tree basic_event)),
    { valid_dynamic_fault_tree_node n l } +
        { ~ valid_dynamic_fault_tree_node n l }.
Proof.
    prove_dec.
    apply List.list_eq_dec, tree_eq_dec, FT_Node_eq_dec.
    apply basic_event_eq_dec.
    apply PeanoNat.Nat.eq_dec. apply Compare_dec.le_dec.
Qed.

Definition valid_dynamic_fault_tree (dft : fault_tree basic_event) :=
    tree_fall valid_dynamic_fault_tree_node dft.

Lemma valid_dynamic_fault_tree_dec:
    forall (dft : fault_tree basic_event),
    { valid_dynamic_fault_tree dft } +
        { ~ valid_dynamic_fault_tree dft }.
Proof.
    apply tree_fall_dec.
    apply valid_dynamic_fault_tree_node_dec.
Qed.


(*|

Dynamic fault tree evaluation
==============================

In this section, we build Dynamic Fault Tree, using Merle's Algebra operators for the fault tree evaluation :cite:t:`merle:tel-00502012`.

|*)

Definition d' : Set := Merle_Algebra.d basic_event.

#[global]
Instance Merle_Basic_Event_Operators : Basic_Event_Operators d' :=
{
    T := d_0 basic_event ;
    F := d_inf basic_event ;

    b_AND := D_AND basic_event ;
    b_ANDl := n_AND basic_event ;

    b_OR := D_OR basic_event ;
    b_ORl := n_OR basic_event ;

    b_PANDl := (fun x => Some (n_PAND basic_event x));
}.

#[global]
Instance Merle_Basic_Event_Operators_Facts
    : Basic_Event_Operators_Facts Merle_Basic_Event_Operators :=
{
    b_ANDl_singleton := Rule_4 basic_event ;
    b_ANDl_concatenate := Rule_8' basic_event ;
    b_ORl_concatenate := Rule_9' basic_event ;
}.

Definition DFT := fault_tree d'.

(*| From these definitions, one can directly built a fault tree, check it is correct, and evaluate it. |*)

Example Basic_DFT : DFT :=
    in_tree (PAND d')
    [ in_tree (BASIC (d_0 basic_event)) [] ;
      in_tree (BASIC (d_0 basic_event)) []].
(*
Fact Basic_DFT_OK : valid_dynamic_fault_tree Basic_DFT.
Proof.
    prove_valid_fault_tree.
Qed.
*)
(*| .. coq:: none |*)

(*| .. coq:: |*)

(*| .. coq:: none |*)
End Dynamic_Fault_Tree.
