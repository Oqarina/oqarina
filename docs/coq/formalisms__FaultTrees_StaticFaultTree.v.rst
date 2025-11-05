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
   Require Import Oqarina.formalisms.Expressions.Propositions.

   Set Implicit Arguments.
   Set Strict Implicit.

******************
Static Fault Trees
******************


A static fault tree, based on Dugan definition, has only three gates: OR, AND, and K-out-of-N. Note that K-out-of-N are rewritten as a collection of OR and AND gates (see :coq:`Rewrite_Fault_Tree_r` in  :doc:`formalisms__FaultTrees_AbstractFaultTree.v` ). We do not consider K-out-of_N gates in the following.

We provide definitions for a valid fault tree (section :ref:`Definitions`). Then, we provide implementations of boolean-valued fault trees (section :ref:`Boolean-valued fault trees`) and float-value fault trees (:ref:`Floating-point valued fault trees`).

Finally, we provide a mapping from a fault tree to an equivalent minimal cutset and show the mapping is sound (:ref:`Minimal cutset of a static fault tree`).

A complete walk-through of this chapter can be found in the examples in :doc:`FaultTrees__FaultTrees_Examples.v`.

.. coq:: none

   Section Static_Fault_Tree.

Definitions
===========

.. coq::

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
           | K_OUT_OF_N _ k => False (* k < List.length l *)
           | FDEP _ => False
           | SPARE _ => False
           | PAND _ => False
           | AbstractFaultTree.AND _ | AbstractFaultTree.OR _=> True
           | NOT _ => List.length l <= 1%nat
       end.

   Lemma valid_static_fault_tree_node_dec:
       forall (n : FT_Node basic_event)
              (l : list (fault_tree basic_event)),
       { valid_static_fault_tree_node n l } +
           { ~ valid_static_fault_tree_node n l }.
   Proof.
       prove_dec.
       apply List.list_eq_dec.
       apply ltree_eq_dec, FT_Node_eq_dec.
       apply basic_event_eq_dec.
       apply Compare_dec.le_dec.
   Qed.

   Definition valid_static_fault_tree
       (sft : fault_tree basic_event)
   :=
       ltree_fall valid_static_fault_tree_node sft.

   Lemma valid_static_fault_tree_dec:
       forall (sft : fault_tree basic_event),
       { valid_static_fault_tree sft } +
           { ~ valid_static_fault_tree sft }.
   Proof.
       apply ltree_fall_dec.
       apply valid_static_fault_tree_node_dec.
   Qed.

   Fixpoint valid_static_fault_tree'
       (f : fault_tree basic_event)
   :=
       let 'ltree_cons x ll := f in
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
       - induction l.
           * simpl ; auto.
           * simpl. apply dec_sumbool_and.
               + apply X ; simpl ; auto.
               + apply IHl. auto with *.
   Qed.

We prove vairous auxiliary results on :coq:`valid_static_fault_tree'` that are useful for proof by induction.

.. coq::

   Lemma valid_static_fault_tree'_children:
       forall a ll,
           valid_static_fault_tree' (ltree_cons a ll) ->
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
       valid_static_fault_tree' (ltree_cons a (a0 ::ll)) ->
       valid_static_fault_tree' a0.
   Proof.
       intros.
       apply valid_static_fault_tree'_children
           with (a:=a) (ll:=a0::ll).
       apply H. apply in_eq.
   Qed.

   Lemma valid_static_fault_tree'_cons: forall a a0 ll,
       valid_static_fault_tree' (ltree_cons a (a0 ::ll)) ->
       valid_static_fault_tree' (ltree_cons a ll).
   Proof.
       intros.
       unfold valid_static_fault_tree' in *.
       simpl in H.
       intuition.

       generalize H0.
       unfold valid_static_fault_tree_node.
       case a ; auto with *. intros. inversion H1.
   Qed.

We show that :coq:`Rewrite_Fault_Tree` and :coq:`Rewrite_Fault_Tree''`preserve the notion of validity of a fault tree.

.. coq::

   Lemma valid_Rewrite_Fault_Tree:
       forall (f: fault_tree basic_event),
           valid_static_fault_tree' f ->
               valid_static_fault_tree' (Rewrite_Fault_Tree f).
   Proof.
       intros.
       induction f.
       destruct x ; trivial.

       (* OR gates *)
       - induction l.
           * simpl ; intuition.
           * unfold Rewrite_Fault_Tree. destruct l.
               + apply H.
               + destruct l; destruct f ; trivial.
                 destruct l0 ; intuition. simpl in *. intuition.

       (* AND gates *)
       - induction l.
           * simpl ; intuition.
           * unfold Rewrite_Fault_Tree. destruct l.
             + simpl in H. intuition.
             + destruct l; trivial. destruct f ; trivial.
                 destruct l0 ; auto. simpl in *. intuition.
   Qed.

   Lemma valid_Rewrite_Fault_Tree'':
       forall (f: fault_tree basic_event),
           valid_static_fault_tree' f ->
               valid_static_fault_tree' (Rewrite_Fault_Tree'' f).
   Proof.
       intros.
       induction f.
       rewrite Rewrite_Fault_Tree''_fix.
       apply valid_Rewrite_Fault_Tree.

       simpl in *. intuition.

       - destruct x ; intuition.
         simpl. simpl in H1. subst. intuition.
         simpl. simpl in H1.
         assert ( Datatypes.length (map (Rewrite_Fault_Tree'' (basic_event:=basic_event)) l) = Datatypes.length l ).
         apply map_length. rewrite H at 1. auto.

       - induction l ; simpl ; intuition.
         + apply H0 ; auto with *. destruct H2. auto.
         + apply IHl ; auto with *.
           * destruct x ; intuition.
               -- simpl in H1. contradict H1. discriminate.
               -- simpl in H1. simpl. auto with *.
           * destruct H2. apply H2.
   Qed.

.. coq:: none

   End Static_Fault_Tree.

   Section Fault_Tree_Bool.

Boolean-valued fault trees
==========================

One basic way to use abstract fault trees is to instantiate basic events as booleans.

.. coq::

   #[global]
   Instance bool_Basic_Event_Operators : Basic_Event_Operators bool :=
   {
       T := true ;
       F := false ;

       b_AND := andb ;
       b_ANDl := andbl ;

       b_OR := orb ;
       b_ORl := orbl ;

       b_NOT := negb ;

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

.. coq:: none

   End Fault_Tree_Bool.

   Section Results.

We show that rewriting a fault tree (:coq:`Rewrite_Fault_Tree` and :coq:`Rewrite_Fault_Tree''`) preserves the value computed by :coq:`Compute_Fault_Tree_2`.

.. coq::

   Variable basic_event : Set.

   Lemma Compute_Rewrite_Fault_Tree_sound:
       forall (f: fault_tree basic_event) v,
           Compute_Fault_Tree_2 f v =
           Compute_Fault_Tree_2 (Rewrite_Fault_Tree f) v.
   Proof.
       intros.
       induction f.
       case x ; trivial.

       (* OR gates *)
       - induction l.
           * simpl ; reflexivity.
           * unfold Rewrite_Fault_Tree. destruct l.
               + reflexivity.
               + destruct l; trivial. destruct f ; trivial.
                 destruct l0 ; auto. simpl.
                 rewrite orbl_concatenate ; reflexivity.

       (* AND gates *)
       - induction l.
           * simpl ; reflexivity.
           * unfold Rewrite_Fault_Tree. destruct l.
               + reflexivity.
               + destruct l; trivial. destruct f ; trivial.
                 destruct l0 ; auto. simpl.
                 rewrite andbl_concatenate ; reflexivity.
   Qed.

   Lemma Compute_Rewrite_Fault_Tree''_sound:
       forall (f: fault_tree basic_event) (v: basic_event -> bool),
           Compute_Fault_Tree_2 f v =
           Compute_Fault_Tree_2 (Rewrite_Fault_Tree'' f) v.
   Proof.
       intros.

       induction f.
       rewrite Rewrite_Fault_Tree''_fix.
       rewrite <- Compute_Rewrite_Fault_Tree_sound.
       repeat rewrite Compute_Fault_Tree_2_fix.
       rewrite map_map.
       f_equal.
       apply map_ext_in, H.
   Qed.

.. coq:: none

   End Results.

   Section Fault_Tree_Float.

Floating-point valued fault trees
=================================

.. coq::

   Definition f_AND (f1 f2: float) := f1 * f2.
   Definition f_OR (f1 f2: float) := f1 + f2.

   Definition f_NOT (f : float) := 1.0 - f.

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

       b_NOT := f_NOT ;

       b_PANDl := (fun x => None) ;
   }.

.. coq:: none

   End Fault_Tree_Float.

Mapping static fault trees to Boolean Expressions
=================================================

.. coq:: none

   Section Fault_Tree_to_Bool_Expr.

.. coq::

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

   Lemma Map_to_OR_is_Boolean_Expr:
       forall  (l : list (PropF basic_event)),
       (forall x, In x l -> is_Boolean_Expr x) ->
       is_Boolean_Expr (Map_to_OR l).
   Proof.
       intros.
       induction l ; simpl ; auto with *.
   Qed.

   Fixpoint Map_to_AND
       (l : list (PropF basic_event))
       : PropF basic_event
   :=
       match l with
           | nil => Top basic_event
           | h :: t => Conj h (Map_to_AND t)
       end.

   Lemma Map_to_AND_is_Boolean_Expr:
       forall  (l : list (PropF basic_event)),
       (forall x, In x l -> is_Boolean_Expr x) ->
       is_Boolean_Expr (Map_to_AND l).
   Proof.
       intros.
       induction l ; simpl ; auto with *.
   Qed.

   Definition Map_to_NOT
       (l : list (PropF basic_event))
       : PropF basic_event
   :=
       match l with
       | nil => Bot basic_event
       | h :: t => Neg h
   end.

   Lemma Map_to_NOT_is_Boolean_Expr:
       forall  (l : list (PropF basic_event)),
       (forall x, In x l -> is_Boolean_Expr x) ->
       is_Boolean_Expr (Map_to_NOT l).
   Proof.
       intros.
       induction l ; simpl ; auto with *.
   Qed.

   Definition Map_Fault_Node_to_BoolExpr
       (n : FT_Node basic_event)
       (l : list (PropF basic_event))
       : PropF basic_event
   :=
       match n with
           | BASIC b => Var b
           | OR _     => Map_to_OR l
           | AND _    => Map_to_AND l
           | NOT _ => Map_to_NOT l
           | K_OUT_OF_N  _ k =>
              Map_to_OR (map (fun x => Map_to_AND x) (k_of_N k l))
           | _        => Bot basic_event
   end.

   Fixpoint Map_Fault_Tree_to_BoolExpr'
       (f : fault_tree basic_event)
       : PropF basic_event
   :=
       let 'ltree_cons x ll := f in
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
       case x ; intuition ; induction l.

       (* OR *)
       - intuition.

       - assert (forall x, In x l -> valid_static_fault_tree' x ->
                   Compute_Fault_Tree_2 x v =
                   Eval_PropF v (Map_Fault_Tree_to_BoolExpr' x)).
        auto with *. (* Consequence of H0 *)

        assert (Compute_Fault_Tree_2 (ltree_cons (OR basic_event) l) v =
           Eval_PropF v
               (Map_to_OR
               (map (Map_Fault_Tree_to_BoolExpr') l))).
        apply IHl. apply H1.

        apply valid_static_fault_tree'_cons in H0. apply H0.

        simpl. rewrite orbl_cons.

        assert (Compute_Fault_Tree_2 a v =
                   Eval_PropF v (Map_Fault_Tree_to_BoolExpr' a)).
        apply H. apply in_eq.

        apply valid_static_fault_tree'_car in H0. apply H0.

        rewrite H3. rewrite <- H2.
        intuition.

       (* AND *)
       - intuition.

       - assert (forall x, In x l -> valid_static_fault_tree' x ->
                   Compute_Fault_Tree_2 x v =
                   Eval_PropF v (Map_Fault_Tree_to_BoolExpr' x)).
         auto with *. (* Consequence of H0 *)

        assert (Compute_Fault_Tree_2 (ltree_cons (AND basic_event) l) v =
           Eval_PropF v
               (Map_to_AND
               (map (Map_Fault_Tree_to_BoolExpr') l))).
        apply IHl. apply H1.
        apply valid_static_fault_tree'_cons in H0. apply H0.

        simpl. rewrite andbl_cons.

        assert (Compute_Fault_Tree_2 a v =
                   Eval_PropF v (Map_Fault_Tree_to_BoolExpr' a)).
        apply H. apply in_eq.

        apply valid_static_fault_tree'_car in H0. apply H0.

        rewrite H3. rewrite <- H2.
        intuition.

       (* NOT *)
       - intuition.
       - simpl.
         f_equal. apply H ; auto with *.
         apply valid_static_fault_tree'_car in H0. apply H0.

        (* K_OUT_OF_N *)
        - simpl in H0. intuition.
        - simpl in H0. intuition.
   Qed.

   Fixpoint Map_BoolExpr_to_Fault_Tree
       (b : PropF basic_event)
       : fault_tree basic_event
   :=
       match b with
           | Var b => ltree_cons (BASIC b) []

           | Conj b1 b2 => ltree_cons (AND _)
               [ Map_BoolExpr_to_Fault_Tree b1 ;
                 Map_BoolExpr_to_Fault_Tree b2 ]

           | Disj b1 b2 => ltree_cons (OR _)
               [ Map_BoolExpr_to_Fault_Tree b1 ;
                 Map_BoolExpr_to_Fault_Tree b2 ]

           | Neg b1 => ltree_cons (NOT _)
               [ Map_BoolExpr_to_Fault_Tree b1 ]

           | _ => invalid_tree basic_event
       end.

   Lemma Map_BoolExpr_to_Fault_Tree_sound:
       forall (p: PropF basic_event) (v : basic_event -> bool),
           is_Boolean_Expr p ->
               Compute_Fault_Tree_2 (Map_BoolExpr_to_Fault_Tree p) v =
               Eval_PropF v p.
   Proof.
       intros p v i.
       induction p.

       (* Var *)
       - simpl. intuition.

       (* Bot *)
       - simpl. intuition.

       (* Conj *)
       - simpl. rewrite IHp1, IHp2. intuition. destruct i. auto. destruct i. auto.

       (* Disj *)
       - simpl. rewrite IHp1, IHp2. intuition. destruct i. auto. destruct i. auto.

       (* Impl *)
       - destruct i. (* contradiction *)

       (* Neg *)
       - simpl. f_equal. intuition.
   Qed.

.. coq:: none

   End Fault_Tree_to_Bool_Expr.

Minimal cutset of a static fault tree
=====================================

.. coq:: none

   Section Minimal_cutset.

From all these definitions, we can finally go to the final interesting result. First, we define :coq:`Map_Fault_Tree_to_Cutset_PropF`  that maps a fault tree to a proposition. Then, we show that it computes to the same original fault tree in :coq:`Map_Fault_Tree_to_Cutset_PropF_sound`. Then, we build similar lemmas for cutset expressed as fault trees.

The final interesting theorem is :coq:`Map_Fault_Tree_to_Cutset_sound`.

.. coq::

   Variable basic_event : Set.
   Variable basic_event_beq: basic_event → basic_event → bool.
   Hypothesis basic_event_eq_dec : forall x y : basic_event,
       { x = y } + { x <> y }.
   Hypothesis basic_event_reflect: forall x y,
       reflect (x = y) (basic_event_beq x y).

   Definition Map_Fault_Tree_to_Cutset'_PropF
       (f : fault_tree basic_event)
       : PropF basic_event
   :=
       Rewrite_PropF_r
           (PropF_to_cutset basic_event_beq (Map_Fault_Tree_to_BoolExpr' f)).

   Definition Map_Fault_Tree_to_Cutset_PropF
       (f : fault_tree basic_event)
       : PropF basic_event
   :=
       Map_Fault_Tree_to_Cutset'_PropF (Rewrite_Fault_Tree'' f).

   Lemma Map_Fault_Tree_to_Cutset'_PropF_sound:
       forall (f: fault_tree basic_event) v,
           valid_static_fault_tree' f ->
               Compute_Fault_Tree_2 f v =
               Eval_PropF v (Map_Fault_Tree_to_Cutset'_PropF f).
   Proof.
       intros.
       unfold Map_Fault_Tree_to_Cutset'_PropF.

       rewrite Map_Fault_Tree_to_BoolExpr'_sound ; auto.
       rewrite PropF_to_cutset_sound with (PropVars_beq := basic_event_beq) ; auto.
       rewrite Rewrite_PropF_r_Sound.

       reflexivity.
   Qed.

   Lemma Map_Fault_Tree_to_Cutset_PropF_sound:
       forall (f: fault_tree basic_event) v,
           valid_static_fault_tree' f ->
               Compute_Fault_Tree_2 f v =
               Eval_PropF v (Map_Fault_Tree_to_Cutset_PropF f).
   Proof.
      intros.
      unfold Map_Fault_Tree_to_Cutset_PropF.
      rewrite <- Map_Fault_Tree_to_Cutset'_PropF_sound ; auto.
      apply Compute_Rewrite_Fault_Tree''_sound.
      apply valid_Rewrite_Fault_Tree''.
      apply H.
   Qed.

   Definition Map_Fault_Tree_to_Cutset
       (f : fault_tree basic_event)
       : fault_tree basic_event
   :=
       Rewrite_Fault_Tree''
       (Map_BoolExpr_to_Fault_Tree (Map_Fault_Tree_to_Cutset_PropF  f)).

   Lemma is_Boolean_Expr_Map_Fault_Tree_to_BoolExpr':
       forall  (f : fault_tree basic_event),
           valid_static_fault_tree' f ->
           is_Boolean_Expr (Map_Fault_Tree_to_BoolExpr' f).
   Proof.
       intros.
       induction f.
       destruct x ; simpl ; intuition.

       - apply Map_to_OR_is_Boolean_Expr.
         intro x.
         rewrite in_map_iff.
         intros.
         destruct H, H1.
         simpl in *. destruct H1. subst.
         apply H0. auto.
         rewrite <- All_In in H2. auto.

       - apply Map_to_AND_is_Boolean_Expr.
         intro x.
         rewrite in_map_iff.
         intros.
         destruct H, H1.
         simpl in *. destruct H1. subst.
         apply H0. auto.
         rewrite <- All_In in H2. auto.

       - apply Map_to_NOT_is_Boolean_Expr.
         intro x.
         rewrite in_map_iff.
         intros.
         destruct H, H1.
         simpl in *. destruct H1. subst.
         apply H0. auto.
         rewrite <- All_In in H2. auto.

       - destruct H. destruct H.
   Qed.

   Lemma Map_Fault_Tree_to_Cutset_sound:
       forall (f: fault_tree basic_event) (v : basic_event -> bool),
           valid_static_fault_tree' f ->
               Compute_Fault_Tree_2 f v =
               Compute_Fault_Tree_2 (Map_Fault_Tree_to_Cutset f) v.
   Proof.
       intros.
       unfold Map_Fault_Tree_to_Cutset.

       assert (
       Compute_Fault_Tree_2
       (Map_BoolExpr_to_Fault_Tree (Map_Fault_Tree_to_Cutset_PropF f)) v =
       Eval_PropF v (Map_Fault_Tree_to_Cutset_PropF f)).

       apply Map_BoolExpr_to_Fault_Tree_sound ; auto.
       unfold Map_Fault_Tree_to_Cutset_PropF.
       unfold Map_Fault_Tree_to_Cutset'_PropF.
       apply is_Boolean_Expr_Rewrite_PropF_r.
       apply is_Boolean_Expr_PropF_to_cutset.

       apply is_Boolean_Expr_Map_Fault_Tree_to_BoolExpr'.
       apply valid_Rewrite_Fault_Tree'', H.
       rewrite <- Compute_Rewrite_Fault_Tree''_sound.
       rewrite H0.
       apply Map_Fault_Tree_to_Cutset_PropF_sound, H.
   Qed.

.. coq:: none

   End  Minimal_cutset.
