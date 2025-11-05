.. coq::


.. coq:: none

   (* Coq Library *)
   Require Import List.

   Require Export Oqarina.formalisms.FaultTrees.AbstractFaultTree.
   Require Export Oqarina.formalisms.FaultTrees.StaticFaultTree.
   Require Export Oqarina.formalisms.FaultTrees.DynamicFaultTree.

***********
Fault Trees
***********

In this section, we provide a mechanization of fault trees.

* :doc:`formalisms__FaultTrees_AbstractFaultTree.v` provides generic definitions about fault trees.

* :doc:`formalisms__FaultTrees_StaticFaultTree.v` provides an instantiation for static fault trees.

* :doc:`formalisms__FaultTrees_DynamicFaultTree.v` provides an instantiation for dynamic fault trees.

Here is the detailed list of contents:

.. toctree::
   :maxdepth: 2

   formalisms__FaultTrees_AbstractFaultTree.v.rst
   formalisms__FaultTrees_StaticFaultTree.v.rst
   formalisms__FaultTrees_DynamicFaultTree.v.rst

.. coq:: none

   Ltac prove_valid_static_fault_tree :=
       repeat match goal with
       | [ |- forall x : ?T, _ ] => intros t H ; destruct H ; subst
       | [ |- valid_static_fault_tree _ ] => unfold valid_static_fault_tree
       | [ |- valid_static_fault_tree' _ ] =>
           unfold valid_static_fault_tree' ; compute ; firstorder
       | [ |- valid_dynamic_fault_tree _ ] => unfold valid_dynamic_fault_tree
       | [ |- ltree_fall _ _ ] => apply ltree_fall_fix
       | [ |-  _ /\ _ ] => split
       | [ |- valid_static_fault_tree_node  _ _ ] => compute; auto
       | [ |- valid_dynamic_fault_tree_node  _ _ ] => compute; auto
       | [ H : In _ _ |- _ ] => destruct H ; subst
   end.
