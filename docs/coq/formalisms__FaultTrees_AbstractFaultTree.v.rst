.. coq::


.. coq:: none

   (* Coq Library *)
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Coq.Relations.Relation_Definitions.
   Require Import Coq.Relations.Relation_Operators.
   Require Import Coq.Unicode.Utf8.
   Require Import Coq.Bool.Bool.

   (* KruskalTrees: provide all the core theories for uniform trees as lists of
   trees with induction principles and related results. *)
   Require Export KruskalTrees.tree.ltree.

   (* Oqarina Library*)
   Require Import Oqarina.coq_utils.all.
   Require Import Oqarina.core.all.
   Require Import Oqarina.formalisms.Expressions.all.

   Set Implicit Arguments.
   Set Strict Implicit.

********************
Abstract Fault Trees
********************

In this module, we provide a general definition of fault trees as an inductive type (section :ref:`Definition`).

Then, we introduce reduction functions that rewrite fault trees using simpler terms (section :ref:`Reduction of Fault Trees`). We first define reduction rules, then a function that implements these transformations. We show the transformation is sound.

In section :ref:`Evaluation of a fault tree`, we define a generic evaluation function for fault trees as a typeclass. This function can be specialized for various types (e.g. boolean, floats, ...).

.. coq:: none

   Section Abstract_Fault_Tree.

Definition
==========

We define a fault tree as an AST over FT_Node, a type representing the various gates of a fault tree. Each gate  (AND, OR, ...) represents a combinatorial function of some basic events.

A basic event is defined as a generic type, equipped with a decidable equality and a boolean equality.

.. coq::

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
       | NOT
       | PAND
       | SPARE
       | FDEP
       | K_OUT_OF_N (k : nat).

   Lemma FT_Node_eq_dec : forall x y : FT_Node,
       { x = y } + { x <> y }.
   Proof.
       repeat decide equality.
   Qed.

   Definition fault_tree := ltree FT_Node.

   Definition invalid_tree := ltree_cons INVALID [].

:coq:`Get_Root_FT_Node` returns the FT_Node of the root of a fault tree.

.. coq::

   Definition Get_Root_FT_Node (f : fault_tree) :=
       match f with
       | ltree_cons n _ => n
       end.

.. coq:: none

   Section Fault_Tree_Expansion.

.. coq::

   Definition Expand_Fault_Tree (F : fault_tree)
       : fault_tree
       :=
   match F with
       (* red_K_OUT_OF_N *)
       | ltree_cons (K_OUT_OF_N k) l =>
           ltree_cons OR (map (fun x => ltree_cons AND x) (k_of_N k l))

       (* tauto *)
       | _ => F
   end.

A direct result of :coq:`Expand_Fault_Tree'` is that the K_OUT_OF_N gate has been suppressed.

Note: here we use some intermediate lemmas to leverage :coq:`ltree_fall` (forall for a ltree).

.. coq::

   Definition Expand_Fault_Tree_postcondition_def f: Prop :=
       forall k, Get_Root_FT_Node (Expand_Fault_Tree f)
       <> K_OUT_OF_N k.

   Lemma Expand_Fault_Tree_postcondition:
       forall (f : fault_tree), Expand_Fault_Tree_postcondition_def f.
   Proof.
       induction f.
       case x ;simpl ; try discriminate.
   Qed.

   Definition Expand_Fault_Tree_postcondition_def_2
       (X: FT_Node) (l: list (ltree FT_Node)) :=
       Expand_Fault_Tree_postcondition_def (ltree_cons X l).

   Lemma Expand_Fault_Tree_postcondition_2:
       forall (X: FT_Node) (l: list (ltree FT_Node)),
       Expand_Fault_Tree_postcondition_def_2 X l.
   Proof.
       intros.
       apply Expand_Fault_Tree_postcondition.
   Qed.

   Fixpoint Expand_Fault_Tree' (f : fault_tree) :=
       let 'ltree_cons x ll := f in
       Expand_Fault_Tree
           (ltree_cons x (map Expand_Fault_Tree' ll)).

   Lemma Expand_Fault_Tree'_postcondition:
       forall (f: fault_tree),
           ltree_fall Expand_Fault_Tree_postcondition_def_2 f.
   Proof.
       induction f.
       apply ltree_fall_fix.
       split.
       apply Expand_Fault_Tree_postcondition_2.
       apply H.
   Qed.

.. coq:: none

   End Fault_Tree_Expansion.

   Section Fault_Tree_Reduction.

Reduction of Fault Trees
========================

A Fault Tree can generally be reduced through specifc tree transformations. In this section, we first define those lemmas as propositions (in :coq:`red`), then provide an implementation of those reduction rules (:coq:`Rewrite_Fault_Tree` and :coq:`Rewrite_Fault_Tree_r`)  and show they are correctly implemented.

.. coq::

   Inductive red : relation (fault_tree) :=
       | red_AND_1: forall (a: fault_tree),
           red (ltree_cons AND [a]) (a)

       | red_AND_concatenate: forall a l,
           red (ltree_cons AND [a; ltree_cons AND l])
               (ltree_cons AND (a :: l))

       | red_OR_concatenate: forall a l,
           red (ltree_cons OR [a; ltree_cons OR l])
               (ltree_cons OR (a :: l)).

   Definition Rewrite_Fault_Tree (F : fault_tree)
       : fault_tree
       :=
   match F with
       (* red_AND_concatenate *)
       | ltree_cons AND [a; ltree_cons AND l] =>
           ltree_cons AND (a :: l)

       (* red_OR_concatenate *)
       | ltree_cons OR [a; ltree_cons OR l] =>
           ltree_cons OR (a :: l)

       (* red_AND_1 *)
       | ltree_cons AND (h :: []) => h

       (* tauto *)
       | _ => F
   end.

First, we demonstrate that :coq:`Rewrite_Fault_Tree` is sound, that is for all pair (f, f') of fault trees, if f' is a reduction of  f, then it can be computed by executing :coq:`Rewrite_Fault_Tree`.

.. coq::

   Lemma Rewrite_Fault_Tree_Sound : forall (f f': fault_tree),
       red f f' -> Rewrite_Fault_Tree f = f'.
   Proof.
       intros.
       inversion H ; simpl ; intuition.
   Qed.

Then the opposite lemma.

.. coq::

   Lemma Rewrite_Fault_Tree_Complete' :
       forall (f : fault_tree),
           clos_refl_trans _ red f (Rewrite_Fault_Tree f).
   Proof.
       intros.
       induction f.
       case x.

       (* INVALID *)
       - intros. simpl. apply rt_refl.

       (* BASIC *)
       - intros. simpl. apply rt_refl.

       (* OR *)
       - simpl. case l.
           * apply rt_refl.
           * intros. case l1.
               + apply rt_refl.
               + intros. case l3.
                   ** destruct l2, f ; try apply rt_refl.
                       apply rt_step, red_OR_concatenate.
                   ** intros. destruct l2.
                      destruct f ; apply rt_refl.

       (* AND *)
       - simpl. case l.
           * apply rt_refl.
           * intros. case l1.
               + apply rt_step, red_AND_1.
               + intros. destruct l2, f ; try apply rt_refl.
                 case l3.
                   ** apply rt_step, red_AND_concatenate.
                   ** intros. destruct l0. destruct f ; apply rt_refl.

       (* NOT *)
       - simpl. apply rt_refl.

       (* PAND *)
       - simpl. apply rt_refl.

       (* SPARE *)
       - simpl. apply rt_refl.

       (* FDEP *)
       - simpl. apply rt_refl.

       (* K_OUT_OF_N *)
       - intros. simpl. apply rt_refl. (*apply rt_step, red_K_OUT_OF_N.*)
   Qed.

   Lemma Rewrite_Fault_Tree_Complete : forall (f f': fault_tree),
       Rewrite_Fault_Tree f = f' ->
           clos_refl_trans _  red f f'.
   Proof.
       intros. subst. apply Rewrite_Fault_Tree_Complete'.
   Qed.

Finally, we define recursive functions that apply the reduction to all nodes.

.. coq::

   Definition Rewrite_Fault_Tree' : fault_tree -> fault_tree.
   Proof.
       induction 1 as [ x y IH ] using ltree_recursion.
       apply (Rewrite_Fault_Tree (ltree_cons x IH)).
   Defined.

   Fixpoint Rewrite_Fault_Tree'' (f : fault_tree) :=
       let 'ltree_cons x ll := f in
       Rewrite_Fault_Tree
           (ltree_cons x (map Rewrite_Fault_Tree'' ll)).

   Lemma Rewrite_Fault_Tree''_fix: forall x ll,
       Rewrite_Fault_Tree'' (ltree_cons x ll) =
           Rewrite_Fault_Tree
               (ltree_cons x (map Rewrite_Fault_Tree'' ll)).
   Proof. trivial. Qed.

.. coq:: none

   End Fault_Tree_Reduction.

   Section Fault_Tree_Evaluation.

Evaluation of a fault tree
==========================

In this section, we define a generic function :coq:`Compute_Fault_Node` that evaluates the value of a fault node. It is parameterized by the typeclass :coq:`Basic_Event_Operators` that provides basic operators for a given type and :coq:`Basic_Event_Operators_Facts` that provides associated lemmas.

We latter provide instances for booleans, floats, etc.

.. coq:: none

   Section FT_Operators.

.. coq::

   Class Basic_Event_Operators (A : Type):=
   {
       T : A ;
       F : A ;

       b_AND : A -> A -> A ;
       b_OR : A -> A -> A ;
       b_NOT : A -> A ;

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

.. coq:: none

   End FT_Operators.

We define :coq:`Compute_Fault_Node` as a generic function that relies on instance of :coq:`Basic_Event_Operators` and :coq:`Basic_Event_Operators_Facts`.

.. coq::

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
           | NOT => match l' with
                   | [] => None
                   | h::t => Some (b_NOT h)
                   end
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
           | NOT => match l with
               | [] => F
               | h::t => b_NOT h
               end
           | K_OUT_OF_N k => b_k_out_of_N k l
           | FDEP => F
           | PAND => F (* XXX *)
           | SPARE => F
       end.

   Fixpoint Compute_Fault_Tree''
       (f : fault_tree ) v
       : option basic_event_value
   :=
        let 'ltree_cons x ll := f in
           Compute_Fault_Node x v
               (map (fun x => Compute_Fault_Tree'' x v) ll).

   Fixpoint Compute_Fault_Tree_2
       (f : fault_tree ) v
       : basic_event_value
   :=
       let 'ltree_cons x ll := f in
           Compute_Fault_Node_2 x v
               (map (fun x => Compute_Fault_Tree_2 x v) ll).

   Lemma Compute_Fault_Tree_2_fix: forall x ll v,
       Compute_Fault_Tree_2 (ltree_cons x ll) v =
           Compute_Fault_Node_2 x v
               (map (fun x => Compute_Fault_Tree_2 x v) ll).
   Proof. trivial. Qed.

.. coq:: none

   End Fault_Tree_Evaluation.

   End Abstract_Fault_Tree.
