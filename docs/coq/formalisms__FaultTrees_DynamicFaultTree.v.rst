.. coq::


.. coq:: none

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
   Require Import Oqarina.formalisms.Expressions.Propositions.

   Set Implicit Arguments.
   Set Strict Implicit.

*******************
Dynamic Fault Trees
*******************

In the following, we use the fornulation of Dynamic Fault Tree from
:cite:t:`merle:tel-00502012`. One critical aspect is that this formulation assumes that events are non-repairable and that basic events are statistically independent. In addition, the NOT gate cannot be defined.

.. coq::

   Section Dynamic_Fault_Tree.

.. coq::

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
           | NOT _ => False (* Cannot be defined using Merle's algebra *)
       end.

   Lemma valid_dynamic_fault_tree_node_dec:
       forall (n : FT_Node basic_event) (l : list (fault_tree basic_event)),
       { valid_dynamic_fault_tree_node n l } +
           { ~ valid_dynamic_fault_tree_node n l }.
   Proof.
       prove_dec.
       apply List.list_eq_dec, ltree_eq_dec, FT_Node_eq_dec.
       apply basic_event_eq_dec.
       apply PeanoNat.Nat.eq_dec. apply Compare_dec.le_dec.
   Qed.

   Definition valid_dynamic_fault_tree (dft : fault_tree basic_event) :=
       ltree_fall valid_dynamic_fault_tree_node dft.

   Lemma valid_dynamic_fault_tree_dec:
       forall (dft : fault_tree basic_event),
       { valid_dynamic_fault_tree dft } +
           { ~ valid_dynamic_fault_tree dft }.
   Proof.
       apply ltree_fall_dec.
       apply valid_dynamic_fault_tree_node_dec.
   Qed.

Dynamic fault tree evaluation
==============================

In this section, we build Dynamic Fault Tree, using Merle's Algebra operators for the fault tree evaluation :cite:t:`merle:tel-00502012`.

.. coq::

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

       b_NOT := fun x =>  d_inf basic_event ;

       b_PANDl := (fun x => Some (n_PAND basic_event x));
   }.

   #[global]
   Instance Merle_Basic_Event_Operators_Facts
       : Basic_Event_Operators_Facts Merle_Basic_Event_Operators :=
   {
       b_ANDl_singleton := Theorem_4 basic_event ;
       b_ANDl_concatenate := Theorem_8' basic_event ;
       b_ORl_concatenate := Theorem_9' basic_event ;
   }.

   Definition DFT := fault_tree d'.

From these definitions, one can directly built a fault tree, check it is correct, and evaluate it.

.. coq::

   Example Basic_DFT : DFT :=
       ltree_cons (PAND d')
       [ ltree_cons (BASIC (d_0 basic_event)) [] ;
         ltree_cons (BASIC (d_0 basic_event)) []].
   (*
   Fact Basic_DFT_OK : valid_dynamic_fault_tree Basic_DFT.
   Proof.
       prove_valid_fault_tree.
   Qed.
   *)

.. coq:: none

   End Dynamic_Fault_Tree.
